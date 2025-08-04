; highlights.scm

(comment) @comment 
(atom) @atom 
(identifier) @identifier
(base_type) @base_type
(arrow_type
 "->" @symbol)
"(" @paren
")" @paren 
"ref" @keyword 
(fn_expr
  "fn" @keyword
  ":" @symbol 
  "=>" @symbol
)
(pfn_expr
  "pfn" @keyword
  ":" @symbol 
  "=>" @symbol
)
(let_expr
 "let" @keyword
  "=" @symbol
  "in" @keyword)
(while_expr
 "while" @keyword
  "do" @keyword)
(if_expr
 "if" @keyword
  "then" @keyword
  "else" @keyword)
[( "+") ("-") ("*") ("/")(">")(">=")("<")("<=")("==")] @operator
 (ref_expr
 "ref" @keyword)
 (deref_expr
  "!" @symbol)
(assign_expr
 ":=" @symbol)
(app_expr
 (expr) @funcName
 (expr) @arg)


