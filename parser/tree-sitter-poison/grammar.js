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

  conflicts: $ => [
    [$.seq_expr, $.ref_expr],
     [$.seq_expr, $.deref_expr],
     [$.seq_expr, $.assign_expr],
     [$.seq_expr, $.fn_expr],
     [$.seq_expr, $.pfn_expr],
     [$.seq_expr, $.while_expr],
     [$.seq_expr, $.let_expr],
     [$.seq_expr, $.if_expr]
  ],
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
      $.identifier ,
      $.group_expr
    ),
    
    // 1. Sequencing: e1 ; e2
    seq_expr: $ => prec.right(1,seq(
      field("left", $.expr),
      ";",
      field("right", $.expr)
    )),

    // 2. let x = e1 in e2
    let_expr: $ => prec.left(2,seq(
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
                  "unit"
                ),
    

    type_expr: $ => prec.right(seq(
      field("from", choice($.base_type, seq("(", $.type_expr, ")"))),
      optional(seq("->", field("to", $.type_expr)))
    )),
    paren_type: $ => seq("(", $.type_expr, ")"), 

    fn_expr: $ =>  prec.left(2,seq(
        "fn",
        field("param", $.identifier),
        ":",
        field("arg_type",$.type_expr),
        "=>",
        field("body", $.expr),
        ":",
        field("return_type",$.type_expr)
      )),

      pfn_expr: $ =>  prec.left(2,seq(
        "pfn",
        field("param", $.identifier),
        ":",
        field("arg_type",$.type_expr),
        "=>",
        field("body", $.expr),
        ":",
        field("return_type",$.type_expr)
      )),

    // 4. if e1 then e2 else e3
    if_expr: $ => prec.left(2,seq(
      "if",
      field("cond", $.expr),
      "then",
      field("then_branch", $.expr),
      "else",
      field("else_branch", $.expr)
    )),

    // 5. ref e
    ref_expr: $ => prec.left(5,seq(
      "ref",
      field("value", $.expr)
    )),

    // 6. !e (deref)
    deref_expr: $ => prec.left(5,seq(
      "!",
      field("target", $.expr)
    )),

    // 7. application: e1 e2
    app_expr: $ => prec.left(3, seq(
      field("func", $.expr),
      field("arg", $.expr)
    )),

    // 8. binary arithmetic: e1 + e2, e1 > e2, etc.
    binary_expr: $ => prec.left(4, seq(
      field("left", $.expr),
      field("op", choice("+", "-", "*", ">", ">=", "<", "==")),
      field("right", $.expr)
    )),

    // 9. atoms: number, true, false, unit
    atom: $ => prec.left(10,choice(
      $.number,
      "true",
      "false",
      "unit"
    )),

    // WHILE LOOP: while e1 do e2
    while_expr: $ => prec.left(2,seq(
      "while",
      field("cond", $.expr),
      "do",
      field("body", $.expr)
    )),

    // ASSIGNMENT: id := e2
    assign_expr: $ => prec.left(2,seq(
      field("target", $.identifier),
      ":=",
      field("value", $.expr)
    )),

    number: $ => /-?\d+/,
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