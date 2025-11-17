/**
 * @file Poison grammar for tree-sitter
 * @author Jay Choudhary
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "poison",

  extras: $ => [
    /\s/,
    $.comment
  ],

  word: $ => $.identifier, // for syntax highlighting


  rules: {
    source_file: $ => repeat($.expr),

    expr: $ => choice(
      $.seq_expr,
      $.if_expr,
      $.let_expr,
      $.while_expr,
      $.fn_expr,
      $.pfn_expr,
      $.ref_expr,
      $.assign_expr,
      $.deref_expr,
      $.binary_expr,
      $.app_expr,
      $.atom,
      $.identifier,
      $.group_expr,
      $.rand_expr,
      $.frand_expr,
      $.printStr_expr,
      $.printInt_expr,
      $.unary_expr,
      $.boolean_expr,
      $.extern_expr

    ),

    // 1. Sequencing: e1 ; e2
    seq_expr: $ => prec.right(1, seq(
      field("left", $.expr),
      ";",
      field("right", $.expr)
    )),

    // 2. let x = e1 in e2
    let_expr: $ => prec.left(4, seq(
      "let",
      field("name", $.identifier),
      "=",
      field("value", $.expr),
      "in",
      field("body", $.expr)
    )),
    base_type: $ => choice(
      "int",
      "bool",
      "unit", "string"
    ),

    type_expr: $ => choice(
      $.arrow_type,
      $.ref_type,
      $.base_type,
      $.paren_type
    ),

    arrow_type: $ => prec.right(1, seq(
      field("from", $.type_expr),
      "->",
      field("to", $.type_expr)
    )),

    ref_type: $ => prec.left(2, seq(
      "ref",
      field("to", $.type_expr)
    )),
    paren_type: $ => seq("(", $.type_expr, ")"),

    fn_expr: $ => prec.left(4, seq(
      "fn",
      field("param", $.identifier),
      ":",
      field("arg_type", $.type_expr),
      "=>",
      field("body", $.expr),
      ":",
      field("return_type", $.type_expr)
    )),

    pfn_expr: $ => prec.left(2, seq(
      "pfn",
      field("param", $.identifier),
      ":",
      field("arg_type", $.type_expr),
      "=>",
      field("body", $.expr),
      ":",
      field("return_type", $.type_expr)
    )),

    // 4. if e1 then e2 else e3
    if_expr: $ => prec.left(2, seq(
      "if",
      field("cond", $.expr),
      "then",
      field("then_branch", $.expr),
      "else",
      field("else_branch", $.expr)
    )),

    // 5. ref e
    ref_expr: $ => prec.left(7, seq(
      "ref",
      field("value", $.expr)
    )),

    // 6. !e (deref)
    deref_expr: $ => prec.left(7, seq(
      "!",
      field("target", $.expr)
    )),

    // 7. application: e1 e2
    app_expr: $ => prec.left(6, seq(
      field("func", $.expr),
      field("arg", $.expr)
    )),

    // 8. binary arithmetic: e1 + e2, e1 > e2, etc.
    binary_expr: $ => prec.left(5, seq(
      field("left", $.expr),
      field("op", choice("+", "-", "*", "/", ">", ">=", "<", "<=", "==", "&", "!=")),
      field("right", $.expr)
    )),
    unary_expr: $ => prec.left(8, seq(
      field("op", "not"),
      field("value", $.expr)
    )),
    boolean_expr: $ => prec.left(4, seq(
      field("left", $.expr),
      field("op", choice("&&", "||")),
      field("right", $.expr)
    )),


    // 9. atoms: number, true, false, unit
    atom: $ => prec.left(10, choice(
      $.number,
      $.string,
      "true",
      "false",
      "unit"
    )),

    // WHILE LOOP: while e1 do e2
    while_expr: $ => prec.left(2, seq(
      "while",
      field("cond", $.expr),
      "do",
      field("body", $.expr),
      "done"
    )),

    // ASSIGNMENT: id := e2
    assign_expr: $ => prec.left(2, seq(
      field("target", $.identifier),
      ":=",
      field("value", $.expr)
    )),

    //rand expr (rand e)
    rand_expr: $ => prec.left(3, seq(
      "rand",
      choice($.atom, $.group_expr, $.identifier, $.deref_expr))
    ),

    //frand_expr  
    frand_expr: $ => prec.left(3, seq(
      "frand",
      choice($.atom, $.group_expr, $.identifier, $.deref_expr))
    ),
    printStr_expr: $ => prec.left(3, seq(
      "printString",
      choice($.atom, $.group_expr, $.identifier))
    ),
    printInt_expr: $ => prec.left(3, seq(
      "printInt",
      choice($.atom, $.group_expr, $.identifier, $.deref_expr))
    ),

    /*Grammar additions:
 
       Grammar additions:
 
       extern val : (T :> poisoned|clean { guard g, x => pred }) – with guard closure
       extern val : (T :> poisoned|clean { guard g }) – with guard-only
       extern val : (T :> poisoned|clean { no_pred }) – with no predicate
       extern fn a : (ST₁) -> (RET) where RET is either (T₂ :> …) or another extern fn|pfn …
       extern pfn a : (ST₁) -> (RET) with no effects: block
       effects: { !name :> (T :> …), ... } for impure externs
     */


    pexpr: $ => seq(field("name", $.identifier), "=>", field("pred", $.expr)),

    predicate_clause: $ => seq(
      "{",
      optional(seq(
        field("guard", $.number),
        optional(seq(",", field("pexpr", $.pexpr)))
      )),
      "}"),

    poison: $ => choice("poisoned", "clean"),
    qtyp: $ => seq("(",
      $.type_expr, ":>", field("poison", $.poison),
      $.predicate_clause, ")"
    ),

    extern_expr: $ => prec.right(4, choice(
      $.extern_val,
      $.extern_fn,
      $.extern_pfn
    )),

    extern_val: $ => prec.left(seq(
      "extern",
      "val",
      ":",
      field("type", $.qtyp)

    )),

    extern_fn: $ => prec.left(seq(
      "extern",
      "fn",
      field("name", $.identifier),
      ":",
      field("arg_type", $.paren_type),
      "->",
      field("return_type", seq("(", choice($.qtyp, $.extern_fn, $.extern_pfn), ")")),

      optional(seq(",", field("effects", seq("effects", ":", $.effects_block)))
      )
    )),

    extern_pfn: $ => prec.left(seq(
      "extern",
      "pfn",
      field("name", $.identifier),
      ":",
      field("arg_type", $.paren_type),
      "->",
      field("return_type", seq("(", choice($.qtyp, $.extern_fn, $.extern_pfn), ")"))
    )),

    effects_block: $ => seq(
      "{",
      repeat(
        seq(
          field("effect", $.effect),
          optional(",")
        )
      ),
      "}"
    ),

    return_kw: $ => "return",

    effect: $ => seq(
      choice(seq("!",
        field("name", $.identifier)), field("target", $.return_kw)),
      ":>",
      field("type", $.qtyp)
    ),

    number: $ => /-?\d+/,
    string: $ => /"(?:[^"\\]|\\.)*"/,

    group_expr: $ => prec(9, seq(
      "(",
      $.expr,
      ")"
    )),
    // 10. reserved words excluded
    identifier: $ => token(prec(-1, /[a-zA-Z_][a-zA-Z0-9_]*/)),


    comment: $ => token(seq("--", /.*/))

  }
});