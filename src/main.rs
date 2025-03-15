

#[derive(PartialEq, Clone, Debug)]
enum Term {
    Var(String),
    Param(String, Vec<String>),
    Bound(i32),
    Fun(String, Vec<Term>)
}

enum Form {
    Pred(String, Vec<Term>),
    Conn(String, Vec<Form>),
    Quant(String, String, Box<Form>)
}

/*
Meaning of variable names:
    a,b,c: string   q,r: string (quantifier names)
    i,j: int (Bound indexes)
    t,u: term   A,B: form
    x,y: any    f,g: functions
 */

fn map<F,T>(f: F, list: Vec<T>) -> Vec<T>
where F: Fn(T) -> T, {
    list.into_iter().map(f).collect()
}

/*
fun replace_term (u,new) t =
if t=u then new else
case t of Fun(a,ts) => Fun(a, map (replace_term(u,new)) ts)
| _ => t;
 */
/// Replace the atomic term u by new throughout a term
fn replace_term(u_find: Term, new_repl: Term) -> fn(Term) -> Term {
    |t_exam| {
        if t_exam == u_find {
            return new_repl;
        } else {
            match t_exam {
                Term::Fun(a_name, ts_args) =>
                    Term::Fun(a_name, map(replace_term(u_find, new_repl), ts_args)),
                _ => t_exam
            }
        }
    }
}

/*
fun abstract t =
    let fun abs i (Pred(a,ts))   = Pred(a, map (replace_term (t, Bound i)) ts)
          | abs i (Conn(b,As))   = Conn(b, map (abs i) As)
          | abs i (Quant(q,b,A)) = Quant(q, b, abs (i+1) A)
    in abs 0 end;
 */
/// Abstraction of a formula over u (containing no bound vars).
fn abstract_over(t : Term) -> fn(Form) -> Form {
    fn abs (i : i32) -> fn(f: Form) -> Form {
        |f: Form| -> Form {
            match f {
                Form::Pred(a, ts) =>
                    Form::Pred(a, map(
                            replace_term(t, Term::Bound(i)
                        ), ts)),
                   Form::Conn(b, As) => Form::Conn(b, map(abs(i), As)),
                   Form::Quant(s, ts, A) =>
                       Quant(s, ts, Box::new(abs(i + 1)(*A)))
            }
        }
    };

    return abs(0);
}

/*
 fun subst_bound t =
     let fun subst i (Pred(a,ts)) = Pred(a, map (replace_term (Bound i, t)) ts)
         | subst i (Conn(b,As)) = Conn(b, map (subst i) As)
         | subst i (Quant(q,b,A)) = Quant(q, b, subst (i+1) A)
     in subst 0 end;
*/
/// Replace (Bound 0) in formula with t (containing no bound vars).
fn subst_bound(t : Term) -> fn(Form) -> Form {
    fn subst (i : i32) -> fn(f: Form) -> Form {
        |f: Form| -> Form {
            match f {
                Form::Pred(a, ts) =>
                    Form::Pred(a, map(
                        replace_term(Term::Bound(i), t)
                        , ts)),
                Form::Conn(b, As) => Form::Conn(b, map(subst(i), As)),
                Form::Quant(q, b, A) =>
                    Quant(q, b, Box::new(subst(i + 1)(*A)))
            }
        }
    };

    return subst(0);
}

// SYNTAX: SCANNING, PARSING, AND DISPLAY

// Scanning a list of characters into a list of tokens
// datatype token = Key of string | Id of string;
enum Token {
    Key(String), Id(String)
}

// fun is_char(l,c,u) = ord l <= ord c andalso ord c <= ord u;
fn is_char(l:char, c:char, u:char) -> bool {
    (l <= c) && (c <= u)
}

/*
 fun is_letter_or_digit c =
 is_char("A",c,"Z") orelse is_char("a",c,"z") orelse is_char("0",c,"9");
*/
fn is_letter_or_digit(c : char) -> bool {
    is_char('A',c,'Z') || is_char('a',c,'z') || is_char('0',c,'9')
}

// Scanning of identifiers and keywords

//fun token_of a = if a mem ["ALL","EXISTS"] then Key(a) else Id(a);
fn token_of(a : String) -> Token {
    match a.as_str() {
        "ALL"|"EXISTS" => Token::Key(a),
        _ => Token::Id(a)
    }
}

fn implode(cs : Vec<char>) -> String {
    cs.iter().collect()
}

/*
fun scan_ident (front, c::cs) =
        if is_letter_or_digit c
        then scan_ident (c::front, cs)
        else (token_of (implode(rev front)), c::cs)
    | scan_ident (front, []) = (token_of (implode(rev front)), []);
*/
fn scan_ident(mut front: Vec<char>, c_cs : &[char]) -> (Token, &[char]) {
    match &*c_cs {
        [c, cs @ ..] =>
            if is_letter_or_digit(*c) {
                front.push(*c);
                scan_ident(front, cs)
            }
            else {
                //front.reverse();
                (token_of(implode(front)), c_cs )
            }
        ,
        _ => {
            //front.reverse();
            (token_of(implode(front)), &[])
        }
    }
}

// Scanning, recognizing--> and <->, skipping blanks, etc.
/*
 fun scan (front_toks, []) = rev front_toks // end of char list
        // long infix operators
     | scan (front_toks, "-"::"-"::">"::cs) = scan (Key"-->" ::front_toks, cs)
     | scan (front_toks, "<"::"-"::">"::cs) = scan (Key"<->" ::front_toks, cs)
        // blanks, tabs, newlines
     | scan (front_toks, " "::cs) = scan (front_toks, cs)
     | scan (front_toks, "\t"::cs) = scan (front_toks, cs)
     | scan (front_toks, "\n"::cs) = scan (front_toks, cs)
     | scan (front_toks, c::cs) =
         if is_letter_or_digit c then scannext(front_toks, scan_ident([c], cs))
         else scan (Key(c)::front_toks, cs)
 and scannext (front_toks, (tok, cs)) = scan (tok::front_toks, cs);
 */
fn scan(mut front_toks : Vec<Token>, c_cs : &[char]) -> Vec<Token> {
    match c_cs {

        // scan (front_toks, []) = rev front_toks // (end of char list)
        [] => front_toks,

        // long infix operators

        //      | scan (front_toks, "-"::"-"::">"::cs) = scan (Key"-->" ::front_toks, cs)
        ['-', '-', '>', cs @ ..] => {
            front_toks.push(Token::Key("-->".to_string()));
            scan(front_toks, cs)
        },

        //      | scan (front_toks, "<"::"-"::">"::cs) = scan (Key"<->" ::front_toks, cs)
        ['<', '-', '>', cs @ ..] => {
            front_toks.push(Token::Key("<->".to_string()));
            scan(front_toks, cs)
        },

        // blanks, tabs, newlines

        // | scan (front_toks, " "::cs) = scan (front_toks, cs)
        [' ', cs @ ..] => scan(front_toks, cs),

        // | scan (front_toks, "\t"::cs) = scan (front_toks, cs)
        ['\t', cs @ ..] => scan(front_toks, cs),

        // | scan (front_toks, "\n"::cs) = scan (front_toks, cs)
        ['\n', cs @ ..] => scan(front_toks, cs),

        /*      | scan (front_toks, c::cs) =
         if is_letter_or_digit c then scannext(front_toks, scan_ident([c], cs))
         else scan (Key(c)::front_toks, cs) */
        [c, cs @ ..] =>
            if is_letter_or_digit(*c) {
                scan_next(front_toks, scan_ident(vec!(*c), cs))
            }
            else {
                front_toks.push(Token::Key(c.to_string()));
                scan(front_toks, c_cs)
            }
    }
}

// and scannext (front_toks, (tok, cs)) = scan (tok::front_toks, cs);
fn scan_next(mut front_toks : Vec<Token>, tok_cs : (Token, &[char])) -> Vec<Token> {
    let (tok, cs) = tok_cs;
    front_toks.push(tok);
    scan(front_toks, cs)
}

// (*Parsing a list of tokens*)

// The original paper used tuples for parse results, but trying to keep track of whether
// each result held one term or many terms or a token or a form was breaking my brain.
// This really just hides the slice of tokens part, but naming it improves signature readability.
// TODO: make ParseResult propagate errors i.e. integrate with Rust's Result<T,E> type somehow.
struct ParseResult<'a, T> {
    value : T,
    rest : &'a [Token],
}

// fun apfst f (x,toks) = (f x, toks);
fn apfst<F,T,U>(f : F, res : ParseResult<T>) -> ParseResult<U>
where F : FnOnce(T) -> U {
    ParseResult { value: f(res.value), rest: res.rest }
}

// (*Functions for constructing results*)

// fun cons x xs = x::xs;
// Note: as used in "apfst (cons u) ..."
fn cons<T>(x : T) -> fn(xs: Vec<T>) -> Vec<T> {
    |mut xs: Vec<T>| -> Vec<T> {
        xs.push(x);
        xs
    }
}

// fun makeFun fu ts = Fun(fu,ts);
fn make_fun(fu : String) -> fn(Vec<Term>) -> Term {
    |ts : Vec<Term>| {
        Term::Fun(fu, ts)
    }
}

// fun makePred id ts = Pred(id,ts);
fn make_pred(id : String) -> fn(Vec<Term>) -> Form {
    |ts : Vec<Term>| {
        Form::Pred(id, ts)
    }
}

// fun makeNeg A = Conn("~", [A]);
fn make_neg() -> fn(Form) -> Form {
    |a : Form| {
        Form::Conn("~".to_string(), vec![a])
    }
}

// fun makeConn a A B = Conn(a, [A,B]);
fn make_conn(s : String, a : Form) -> fn(Form) -> Form {
    |b : Form| {
        Form::Conn(s, vec![a, b])
    }
}

// fun makeQuant q b A = Quant(q, b, abstract (Fun(b,[])) A);
fn make_quant(q : String, b : String) -> fn(Form) -> Form {
    |a: Form| {
        let fun_b = Term::Fun(b.clone(), vec![]);
        let abs_a = abstract_over(fun_b)(a);
        Form::Quant(q, b, Box::from(abs_a))
    }
}

//  Repeated parsing, returning the list of results

/*
 fun parse_repeat (a,parsefn) (Key(b)::toks) = (*
         if a=b then parse_repeat1 (a,parsefn) toks
         else ([], Key(b)::toks)
     | parse_repeat (a, parsefn) toks = ([], toks)
*/
fn parse_repeat<'a, F>(a : &str, parsefn : F, toks : &'a [Token])
    -> ParseResult<Vec<Term>>
where F : FnOnce(Term) -> Term {
    match toks {
        [Token::Key(b), toks@ ..] =>
            if a==b {
                parse_repeat1(a, parsefn, toks)
            }
            else {
                ParseResult { value:vec![], rest: toks }
            },
        _ => ParseResult { value:vec![], rest: toks }
    }
}

/*
 and parse_repeat1 (a,parsefn) toks =    // <phrase>a...a<phrase>
    let val (u,toks2) = parsefn toks
    in apfst (cons u) (parse_repeat (a, parsefn) toks2) end;
 */
fn parse_repeat1<'a, F>(a : &str, parsefn : F, toks : &'a [Token]) -> ParseResult<Vec<Term>>
where F : FnOnce(&'a [Token]) -> ParseResult<Term> {
    let res = parsefn(toks);
    apfst(cons(res.value), parse_repeat(a, parsefn, res.rest))
}

/*
 fun rightparen (x, Key")"::toks) = (x, toks)
     | rightparen _ = raise ERROR "Symbol ) expected";
*/
fn expect_right_paren<T>(res: ParseResult<T>) -> ParseResult<T> {
    match res.rest {
        [Token::Key(String::from(")")), toks @ ..] =>
            ParseResult { value: res.value, rest: toks },
        _ => panic!("Expected right parenthesis")
    }
}



use std::arch::x86_64::__cpuid;
use anyhow::Result;
use url::form_urlencoded::Parse;
use crate::Form::Quant;

fn main() -> Result<()> {
    use promptly::{prompt, prompt_default, prompt_opt};

    let var = Term::Var("x".to_string());
    let fun = Term::Fun("f".to_string(), vec![var]);

    loop {
        let input : String = prompt(">")?;
        break;
    }

    Ok(())
}
