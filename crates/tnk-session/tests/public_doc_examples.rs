use tnk_core::host::{HostFunctionCatalog, codecs};
use tnk_session::{Eval, Session};

fn lowercase_ascii(input: &[u8]) -> Vec<u8> {
    input.to_ascii_lowercase()
}

fn slug(input: &[u8]) -> Vec<u8> {
    input.to_ascii_lowercase()
}

struct Host {
    session: Session,
    pending: String,
}

impl Host {
    fn push_line(&mut self, line: &str) -> Option<Eval> {
        self.pending.push_str(line);
        self.pending.push('\n');

        if !self.session.input_complete(&self.pending) {
            return None;
        }

        let input = std::mem::take(&mut self.pending);
        Some(self.session.eval(&input, false))
    }
}

const MODEL: &str = r#"
fmod KEY-DATA is
  sorts Worker Mode Token Process Conf .
  subsorts Token Process < Conf .
  ops alice bob : -> Worker [ctor] .
  ops idle waiting inside : -> Mode [ctor] .
  op key : -> Token [ctor] .
  op <_:_> : Worker Mode -> Process [ctor] .
  op none : -> Conf [ctor] .
  op __ : Conf Conf -> Conf
    [ctor assoc comm id: none] .
endfm

mod KEY-SAFE is
  protecting KEY-DATA .
  var W : Worker .
  rl [request] :
    < W : idle > => < W : waiting > .
  rl [enter] :
    key < W : waiting > => < W : inside > .
  rl [leave] :
    < W : inside > => key < W : idle > .
endm
"#;

const QUERY: &str = r#"
search in KEY-SAFE :
  key < alice : idle > < bob : idle >
  =>* REST:Conf
      < alice : inside > < bob : inside > .
"#;

const CONTROLLED: &str = r#"
smod KEY-CONTROL is
  protecting KEY-SAFE .
  strat alice-enters @ Conf .
  sd alice-enters :=
    request[W <- alice] ;
    enter[W <- alice] .
endsm

srewrite in KEY-CONTROL :
  key < alice : idle > < bob : idle >
  using alice-enters .
select KEY-SAFE .
"#;

fn has_diagnostic(eval: &Eval) -> bool {
    eval.output.lines().any(|line| {
        line.starts_with("parse error:")
            || line.starts_with("error:")
            || line.starts_with("warning:")
    })
}

#[test]
fn readme_rust_examples_compile_and_run() {
    let mut session = Session::new();
    session.eval("fmod BOOLISH is sort B . ops t f : -> B . endfm", false);

    let result = session.eval("reduce t .", false);
    assert_eq!(
        result.output,
        "reduce in BOOLISH : t .\nrewrites: 0\nresult B: t"
    );

    let catalog = HostFunctionCatalog::builder()
        .register_typed1(
            "text.uppercase",
            codecs::string(),
            codecs::string(),
            |input| input.to_ascii_uppercase(),
        )
        .expect("register text.uppercase")
        .build();
    let mut session = Session::builder().host_functions(catalog).build();
    let entered = session.eval(
        r#"fmod README-HOST is
             sort String .
             op <Strings> : -> String
               [ctor special (id-hook StringSymbol)] .
             op uppercase : String -> String
               [special (id-hook HostFunctionSymbol (text.uppercase)
                         op-hook stringSymbol (<Strings> : ~> String))] .
           endfm"#,
        false,
    );
    assert_eq!(entered.output, "");
    let reduced = session.eval(r#"reduce in README-HOST : uppercase("Tnk-v1") ."#, false);
    assert!(
        reduced.output.contains(r#"result String: "TNK-V1""#),
        "{}",
        reduced.output
    );
}

#[test]
fn book_rust_examples_compile_and_run() {
    let mut session = Session::new();
    let input = "fmod M is sort S . op a : -> S . endfm";
    let color = false;
    let result = session.eval(input, color);
    assert!(!result.exit);

    let returned = Eval {
        output: "Bye.".into(),
        exit: true,
    };
    assert!(returned.exit);

    let mut session = Session::new();
    let entered = session.eval(
        "fmod BOOLISH is
           sort B .
           ops t f : -> B .
         endfm",
        false,
    );
    assert!(!entered.exit);
    assert_eq!(session.current(), Some("BOOLISH"));
    let reduced = session.eval("reduce t .", false);
    assert_eq!(
        reduced.output,
        "reduce in BOOLISH : t .\n\
         rewrites: 0\n\
         result B: t"
    );

    let mut host = Host {
        session: Session::new(),
        pending: String::new(),
    };
    assert!(host.push_line("reduce in UNKNOWN : term .").is_some());
    host.session.set_stdin("first line\nsecond line\n");

    let catalog = HostFunctionCatalog::builder()
        .register_typed1(
            "text.lowercase-ascii",
            codecs::string(),
            codecs::string(),
            lowercase_ascii,
        )
        .expect("valid unique reducer registration")
        .build();
    let mut session = Session::builder().host_functions(catalog).build();
    let entered = session.eval(
        r#"fmod HOST-TEXT is
             sort String .
             op <Strings> : -> String
               [ctor special (id-hook StringSymbol)] .
             op lowercaseAscii : String -> String
               [special (id-hook HostFunctionSymbol (text.lowercase-ascii)
                         op-hook stringSymbol (<Strings> : ~> String))] .
           endfm"#,
        false,
    );
    assert_eq!(entered.output, "");
    let reduced = session.eval(r#"reduce in HOST-TEXT : lowercaseAscii("TNK-V1") ."#, false);
    assert!(
        reduced.output.contains(r#"result String: "tnk-v1""#),
        "{}",
        reduced.output
    );

    let mut session = Session::new();
    assert!(!has_diagnostic(&session.eval(MODEL, false)));
    let first = session.eval(
        "rewrite [1] in KEY-SAFE :
           key < alice : idle > < bob : idle > .",
        false,
    );
    assert!(!first.exit);
    let next = session.eval("continue 2 .", false);
    assert!(!next.exit);

    let result = session.eval(QUERY, false);
    assert!(!result.exit);
    assert!(!has_diagnostic(&result));
    let controlled = session.eval(CONTROLLED, false);
    assert!(!controlled.exit);
    assert!(!has_diagnostic(&controlled));
    assert_eq!(session.current(), Some("KEY-SAFE"));
}

#[test]
fn cheatsheet_rust_examples_compile_and_run() {
    let mut session = Session::new();
    assert_eq!(
        session
            .eval("fmod M is sort S . op term : -> S . endfm", false)
            .output,
        ""
    );
    let eval = session.eval("reduce in M : term .", false);
    if eval.exit {
        panic!("unexpected exit request");
    }
    assert!(eval.output.contains("result S: term"), "{}", eval.output);

    let catalog = HostFunctionCatalog::builder()
        .register_typed1("text.slug", codecs::string(), codecs::string(), slug)
        .expect("register text.slug")
        .build();
    let mut session = Session::builder().host_functions(catalog).build();
    let entered = session.eval(
        r#"fmod CHEATSHEET-HOST is
             sort String .
             op <Strings> : -> String
               [ctor special (id-hook StringSymbol)] .
             op slug : String -> String
               [special (id-hook HostFunctionSymbol (text.slug)
                         op-hook stringSymbol (<Strings> : ~> String))] .
           endfm"#,
        false,
    );
    assert_eq!(entered.output, "");
    let reduced = session.eval(r#"reduce in CHEATSHEET-HOST : slug("TNK") ."#, false);
    assert!(
        reduced.output.contains(r#"result String: "tnk""#),
        "{}",
        reduced.output
    );
}
