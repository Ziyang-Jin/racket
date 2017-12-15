#lang plai

;; Assignment #7 and Final Exam preparation
;; Power Desugaring

;; TODO: Resolve all of the TODO items below.
;; Note that all tests are correct.
;; When you first run, you'll have MANY failed tests;
;; generally fix errors earlier in the process (parse, desugar, interp)
;; before those later in the process, and you'll find those failure
;; counts go down very quickly.
;;
;; As before, working through this will encourage you to touch
;; on valuable pieces of the interpreter. We encourage you to do
;; more! As two examples, little puzzles where we ask about what
;; expressions are or are not in tail position for particular
;; syntactic forms and why or where we use bindcc make great
;; exam questions!

#|

We're going to build a language that gives us access to most of the
elements we've seen all term.

We'll have numbers, various binary operations, conditionals, and
first-class functions with easy syntax for creating recursive
functions.

We'll also have several distinct types, including booleans and an
interesting variation on lists. Unlike in Racket, our list
constructor cons will defer evaluation of its second argument.
So, we'll get a kind of lazy evaluation out of it.

Finally, we'll have continuations.

We'll represent closures internally as Racket functions, which
will make managing both closures and continuations a bit easier,
although it will also mean that we let Racket do a little bit
of the "heavy lifting" for us.




; EBNF:
<Expr> ::= <number>
         | T | F     ; true and false
         | {<binop> <Expr> <Expr>}
         | {bind { <binding>* } <Expr>}  ; multiple bindings, special fun def'n syntax, recursive reference!
         | {fun {<symbol>+} <Expr>}      ; Curried function of multiple parameters
         | {<Expr> <Expr>+}              ; Curried application of multiple arguments
         | {if <Expr> <Expr> <Expr>}
         | {and <Expr>*}   ; {and} => T; and is "short-circuiting"
         | {or <Expr>*}    ; {or}  => F; or is "short-circuiting"
         | {not <Expr>}
         | {bindcc <symbol> <Expr>} ; continuations
         | {set! <symbol> <Expr>}
         | {begin <Expr>+}
         | {empty? <Expr>}
         | {cons <Expr> <Expr>}  ; as discussed above, defers eval'n of the second expression
         | {first <Expr>}
         | {rest <Expr>}
         | empty
         | <id> ; identifier reference

<binding> ::= { define <id> <Expr> }         ; bind an id to a value
            | { define {<id> <id>*} <Expr>}  ; bind an id to a function value

<binop> ::= + | - | * | / | < | = | > | <= | >=


Notes:
+ {bindcc i e} evaluates e in tail position with i bound to the continuation of the bindcc expr
+ In bind, later bindings' expressions can refer to earlier bindings' identifiers. Furthermore,
  the CURRENT binding's expression can refer recursively to the CURRENT binding's identifier.
+ empty? handles any type of value (producing true only for the empty value). cons allows
  anything both in its first and rest position (i.e., you can construct pairs as well as proper
  lists). However, most other type contexts insist on the specific type they expect, including 
  if (in the first expression), and, or, not, and function application.

T, F, empty, define, all <binop>, and each symbol that introduces a form are all reserved
identifiers as is any identifier that begins with an underscore _.

|#



;;;;;;;;;;;;;;;;;;;;; DATA DEFINITIONS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type SBind
  [vbinding (name symbol?) (expr SAS?)]
  [fbinding (fname symbol?) (params (listof symbol?)) (fbody SAS?)])

(define-type SAS ; surface/sugared abstract syntax
  [s-num (n number?)]
  [s-T]
  [s-F]
  [s-id (name symbol?)]
  [s-binop (op symbol?) (lhs SAS?) (rhs SAS?)]
  [s-bind (bindings (listof SBind?)) (body SAS?)]
  [s-fun (names (listof symbol?)) (body SAS?)]
  [s-app (fexp SAS?) (aexps (listof SAS?))] ; argument expressions (aexps (listof SAS?))
  [s-if (cexp SAS?) (texp SAS?) (eexp SAS?)]
  [s-and (exps (listof SAS?))]
  [s-or (exps (listof SAS?))]
  [s-not (exp SAS?)]
  [s-bindcc (name symbol?) (body SAS?)]
  [s-begin (exps (listof SAS?))]
  [s-set! (name symbol?) (vexp SAS?)]
  [s-is-empty? (exp SAS?)]
  [s-cons (fexp SAS?) (rexp SAS?)]
  [s-first (exp SAS?)]
  [s-rest (exp SAS?)]
  [s-empty])

(define-type DAS ; desugared abstract syntax
  ; We use three internal structures to ensure type safety: d-tag
  ; evaluates its expression (insisting on a closure) and retags it
  ; the tag vt; d-check evaluates its expression and produces
  ; true of the expression's tag matches vt; d-assert evaluates its
  ; expression and produces an error if its tag does not match vt,
  ; otherwise just producing the expression's value.
  [d-tag (vt ValueTag?) (exp DAS?)]
  [d-check (vt ValueTag?) (exp DAS?)]
  [d-assert (vt ValueTag?) (text string?) (exp DAS?)]
  
  [d-num (n number?)]
  [d-id (name symbol?)]
  [d-binop (op symbol?) (lexp DAS?) (rexp DAS?)]   ; many fewer binops than in the surface syntax
  [d-recwith (name symbol?) (named-expr DAS?) (body DAS?)]
  [d-fun (name symbol?) (body DAS?)]
  [d-app (fexp DAS?) (aexp DAS?)]
  [d-if (cexp DAS?) (texp DAS?) (eexp DAS?)]
  [d-bindcc (name symbol?) (body DAS?)]
  [d-set! (name symbol?) (vexp DAS?)])

; We use tagged values to assist in desugaring aggressively while
; still being type safe. The surface language has numbers, booleans,
; non-empty sequences, empty sequences, and closures.
;
; The internal language eliminates booleans (boolTag tagged
; closures), empty sequences (emptyTag tagged closure), and
; non-empty sequences (seqTag tagged closures).
;
; We don't use tags on numbers; so all numeric values can be assumed
; to have the tag unTagged.
(define-type ValueTag
  [unTagged]
  [boolTag]
  [seqTag]
  [emptyTag]
  [errorTag])

(define-type Value 
  [numV (n number?)]
  [closureV (tag ValueTag?) (proc procedure?)])

(define *ERROR_PROC* (lambda (v k) (error "used illegal value")))
(define *ERROR_VALUE* (closureV (errorTag) *ERROR_PROC*))

;; get-value-tag Value -> ValueTag
;; produce the value tag of the value, regardless of its type.
(define (get-value-tag v)
  (type-case Value v
    [numV (_) (unTagged)]
    [closureV (tag _) tag]))

(test (get-value-tag (numV 1)) (unTagged))
(test (get-value-tag (closureV (unTagged) *ERROR_PROC*)) (unTagged))
(test (get-value-tag (closureV (boolTag) *ERROR_PROC*)) (boolTag))


;; build-type-assertion : DAS ValueTag string -> DAS
;; builds a new desugared expression that produces the given error text
;; when d-expr evaluates to a value with any tag besides vt and otherwise
;; produces d-expr's value.
(define (build-type-assertion d-expr vt text)
  (d-assert vt text d-expr))


(test (build-type-assertion (d-id 'x) (boolTag) "testing")
      (d-assert (boolTag) "testing" (d-id 'x)))

                     
                               

;; binops and desugared binops
(define *sbinop* '(+ - * / < <= = > >=))
(define *dbinop* '(+ * / <))

;; reserved words
(define *reserved*
  (append
   *sbinop*
   '(T F  bind define fun if and or not bindcc set!
       begin empty? cons first rest empty)))



;; reserved? : any -> boolean
;; given any sexpression, produces true if s is a reserved word and false otherwise
(define (reserved? s)
  (not (not (and (symbol? s)
                 (or (member s *reserved*)
                     (string-prefix? (symbol->string s) "_"))))))

(test (reserved? '+) true)
(test (reserved? 'set!) true)
(test (reserved? '_anything) true)
(test (reserved? 'anything-else) false)
(test (reserved? 0) false)
(test (reserved? '{hello}) false)


;; valid-id? : any -> boolean
;; produces true if s is a valid identifier (a non-reserved symbol), false otherwise
(define (valid-id? s)
  (and (symbol? s)
       (not (reserved? s))))

(test (valid-id? 0) false)
(test (valid-id? '_anything) false)
(test (valid-id? '+) false)
(test (valid-id? 'map) true)
(test (valid-id? 'foo) true)


;;;;;;;;;;;;;;;;;;;;;;;; PARSING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parse-binding : s-expression -> SBind
;; parse a sexpression representing a (variable or function) binding
;; into the corresponding (variable or function) SBind.
(define (parse-binding binding)
  (match binding
    [(list 'define (? valid-id? name) named-exp)
     (vbinding name (parse named-exp))]
    [(list 'define (list (? valid-id? fname) (? valid-id? fparams) ..1) fbody)
     (fbinding fname fparams (parse fbody))]
    [_ (error 'parse "unable to parse binding: ~a" binding)]))

;; Mutually recursive w/parse; so, tests are below parse.

;; TODO: FIX TWO ERRORS IN THE PARSER

;; parse : s-expression -> SAS
;; parses the given concrete syntax into a surface abstract syntax expression
(define (parse sexp)
  (local [(define (parse sexp)
            (error "do not call parse; call helper insted"))
          
          (define (helper sexp)
            (match sexp
              [(? number?) (s-num sexp)]
              ['T (s-T)]
              ['F (s-F)]
              [(? valid-id?) (s-id sexp)]
              [(list (? (lambda (op) (member op *sbinop*)) bop) lexp rexp)
               (s-binop bop (helper lexp) (helper rexp))]
              [(list 'bind bindings body)
               (s-bind (map parse-binding bindings) (helper body))]
              [(list 'fun (list (? valid-id? params) ..1) body)
               (s-fun params (helper body))]
              [(list 'if cexp texp eexp)
               (s-if (helper cexp) (helper texp) (helper eexp))]
              [(list 'and exps ...) (s-and (map helper exps))]
              ; FIX: (list 'or exps ..1) => (list 'or exps ...)
              [(list 'or exps ...) (s-or (map helper exps))]
              [(list 'not exp) (s-not (helper exp))]
              [(list 'bindcc (? valid-id? name) body)
               (s-bindcc name (helper body))]
              [(list 'set! (? valid-id? name) exp)
               (s-set! name (helper exp))]
              [(list 'begin exps ..1)
               (s-begin (map helper exps))]
              [(list 'empty? exp)
               (s-is-empty? (helper exp))]
              [(list 'cons fexp rexp)
               (s-cons (helper fexp) (helper rexp))]
              [(list 'first exp)
               (s-first (helper exp))]
              [(list 'rest exp)
               (s-rest (helper exp))]
              ['empty (s-empty)]
              [(list fexp aexps ..1)
               ; FIX: (s-app (helper fexp) aexps) => (s-app (helper fexp) (map helper aexps))
               (s-app (helper fexp) (map helper aexps))]
              [(? reserved?) (error 'parse "reserved word in unexpected way: ~a" sexp)]
              
              [_ (error 'parse "unable to parse expression ~a" sexp)]))]
    (helper sexp)))


(test (parse-binding '{define x 1})
      (vbinding 'x (s-num 1)))
(test (parse-binding '{define {f x} x})
      (fbinding 'f (list 'x) (s-id 'x)))
(test (parse-binding '{define {f x y z} x})
      (fbinding 'f (list 'x 'y 'z) (s-id 'x)))

; Duplicate identifiers ARE allowed. Because of the way
; we handle Currying, it's the LAST copy that will shadow
; previous copies.
(test (parse-binding '{define {manyf x y z y w} x})
      (fbinding 'manyf (list 'x 'y 'z 'y 'w) (s-id 'x)))

(test/exn (parse-binding '{define {f} x}) "")    ; fns must have at least one parameter
(test/exn (parse-binding 'x) "")                 ; not a binding
(test/exn (parse-binding '{x 1}) "")             ; not the right form
(test/exn (parse-binding '{define _x 1}) "")     ; reserved ID.. in various places
(test/exn (parse-binding '{define {_f x} x}) "")
(test/exn (parse-binding '{define {f _x} x}) "")

; Basic values and identifiers
(test (parse '1) (s-num 1))
(test (parse 'T) (s-T))
(test (parse 'F) (s-F))
(test (parse 'empty) (s-empty))
(test (parse 'x) (s-id 'x))
(test (parse 'y) (s-id 'y))
(test/exn (parse 'fun) "")
(test/exn (parse 'empty?) "")
(test/exn (parse '+) "")
(test/exn (parse '_foo) "")

; Binding expressions (but parsing individual bindings is tested elsewhere.
(test (parse '{bind {{define x 1}} x})
      (s-bind (list (vbinding 'x (s-num 1))) (s-id 'x)))
(test (parse '{bind {{define {f x} 1}} x})
      (s-bind (list (fbinding 'f '(x) (s-num 1))) (s-id 'x)))
(test (parse '{bind {{define x 1} {define {f x} 1}} x})
      (s-bind (list (vbinding 'x (s-num 1)) (fbinding 'f '(x) (s-num 1))) (s-id 'x)))
(test (parse '{bind {} 1}) (s-bind empty (s-num 1)))

(test/exn (parse '{bind {x 1} x}) "")
(test/exn (parse '{bind {{x 1}} x}) "")
(test/exn (parse '{bind {{x 1}}}) "")
(test/exn (parse '{bind {{define _x 1}} x}) "")

(test (parse '{bindcc k 1}) (s-bindcc 'k (s-num 1)))
(test (parse '{bindcc j j}) (s-bindcc 'j (s-id 'j)))
(test/exn (parse '{bindcc _k 1}) "")
(test/exn (parse '{bindcc k}) "")
(test/exn (parse '{bindcc {k 1} 1}) "")

; binops
(test (parse '{+ 1 2}) (s-binop '+ (s-num 1) (s-num 2)))
(test (parse '{* 3 5}) (s-binop '* (s-num 3) (s-num 5)))
(test (parse '{- 1 2}) (s-binop '- (s-num 1) (s-num 2)))
(test (parse '{/ 1 2}) (s-binop '/ (s-num 1) (s-num 2)))
(test (parse '{< 1 2}) (s-binop '< (s-num 1) (s-num 2)))
(test (parse '{= 1 2}) (s-binop '= (s-num 1) (s-num 2)))
(test (parse '{> 1 2}) (s-binop '> (s-num 1) (s-num 2)))
(test (parse '{<= 1 2}) (s-binop '<= (s-num 1) (s-num 2)))
(test (parse '{>= 1 2}) (s-binop '>= (s-num 1) (s-num 2)))

(test/exn (parse '{* 3}) "")
(test/exn (parse '/) "")

; Function definition/application
(test (parse '{fun {x} x}) (s-fun '(x) (s-id 'x)))
(test (parse '{fun {x y} y}) (s-fun '(x y) (s-id 'y)))
(test (parse '{fun {y y} y}) (s-fun '(y y) (s-id 'y))) ; duplicate IDs are OK

(test/exn (parse '{fun {} x}) "")
(test/exn (parse '{fun {_x} x}) "")
(test/exn (parse '{fun x x}) "")

(test (parse '{f a}) (s-app (s-id 'f) (list (s-id 'a))))
(test (parse '{f a b}) (s-app (s-id 'f) (list (s-id 'a) (s-id 'b))))

(test/exn (parse '{f}) "")

; Conditionals/boolean expressions
(test (parse '{if x y z}) (s-if (s-id 'x) (s-id 'y) (s-id 'z)))
(test (parse '{and}) (s-and empty))
(test (parse '{and T}) (s-and (list (s-T))))
(test (parse '{and T F T}) (s-and (list (s-T) (s-F) (s-T))))
(test (parse '{or}) (s-or empty))
(test (parse '{or T}) (s-or (list (s-T))))
(test (parse '{or T F T}) (s-or (list (s-T) (s-F) (s-T))))
(test (parse '{not T}) (s-not (s-T)))

(test/exn (parse 'if) "")
(test/exn (parse 'and) "")
(test/exn (parse 'or) "")
(test/exn (parse 'not) "")
(test/exn (parse '{if x y}) "")
(test/exn (parse '{if w x y z}) "")
(test/exn (parse '{not x y}) "")
(test/exn (parse '{not}) "")

; set!/begin
(test (parse '{set! x 1}) (s-set! 'x (s-num 1)))
(test (parse '{begin x}) (s-begin (list (s-id 'x))))
(test (parse '{begin x y z}) (s-begin (list (s-id 'x) (s-id 'y) (s-id 'z))))

(test/exn (parse '{set! _x 1}) "")
(test/exn (parse '{set! x}) "")
(test/exn (parse '{begin}) "")

; lists (besides empty)
(test (parse '{empty? x}) (s-is-empty? (s-id 'x)))
(test (parse '{cons x y}) (s-cons (s-id 'x) (s-id 'y)))
(test (parse '{first x}) (s-first (s-id 'x)))
(test (parse '{rest x}) (s-rest (s-id 'x)))

(test/exn (parse '{empty?}) "")
(test/exn (parse '{cons x}) "")
(test/exn (parse '{first}) "")
(test/exn (parse '{rest}) "")


;;;;;;;;;;;;;;;;;;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; TODO: FIX ONE ERROR IN THE BUILTINS
;; NO MATTER WHAT IT MAY SEEM LIKE, there really is only one error in here.
;; Perhaps the other problem that seems like it might be here is actually in
;; the implementation of a desugared syntax construct within the interpreter?

;; We begin with a large number of pre-assembled builtin values that get used below, sometimes repeatedly.

; TRUE and FALSE are two argument functions, where TRUE produces its first argument and FALSE its second.
; BOTH arguments must be thunks.
(define *TRUE* (d-tag (boolTag) (d-fun '_t_thunk (d-fun '_e_thunk (d-app (d-id '_t_thunk) (d-id '_t_thunk))))))
(define *FALSE* (d-tag (boolTag) (d-fun '_t_thunk (d-fun '_e_thunk (d-app (d-id '_e_thunk) (d-id '_e_thunk))))))
(define *builtins*
  (hash
   ; True and False are tagged functions of two arguments that apply the first (T or then) or second (F or else) argument.
   'T *TRUE*
   'F *FALSE*

   ; An empty list is an emptyTagged closure.
   'empty (d-tag (emptyTag) (d-fun '_ignore (d-tag (errorTag) (d-fun '_ignore (d-num 0)))))

   ; empty? produces true on an empty list and false on anything else, whether list or not.
   'empty? (d-fun '_val (d-check (emptyTag) (d-id '_val)))

   ; first and rest simply access the appropriate parts of the cons cell they're given
   ; a cons cell is a function of one argument that expects a selector of two arguments.
   ; the selector's first argument is the car (first) of the cell; its second arg is the
   ; cdr (rest) of the cell.
   ;
   ; Note, however, that these are SEQUENCE cells. So, the rest is NOT the value but a
   ; thunk that will produce the value when evaluated.
   'first (d-fun
           '_cell
           (d-app (build-type-assertion (d-id '_cell) (seqTag) "first can only be used on a cons cell")
                  (d-fun '_first (d-fun '_t_rest (d-id '_first)))))
   'rest (d-fun
          '_cell
          (d-app (build-type-assertion (d-id '_cell) (seqTag) "rest can only be used on a cons cell")
                 ; rest is a thunk; so, we apply it to a dummy argument (itself):
                 (d-fun '_first (d-fun '_t_rest (d-app (d-id '_t_rest) (d-id '_t_rest))))))
   
   ; cons isn't quite a working built-in. So, we give it a reserved name _cons.
   ; given two arguments (the second of which must be a thunk), it produces a seqTag'd
   ; function that expects a selector and applies it to its two arguments (not yet
   ; thawing/unthunking the thunk).
   '_cons (d-fun '_a
                 (d-fun '_b_thunk
                        (d-tag (seqTag)
                               (d-fun '_selector (d-app (d-app (d-id '_selector)
                                                               (d-id '_a))
                                                        ; We don't yet run the thunk.
                                                        (d-id '_b_thunk))))))
   
   ; Writing - in terms of + and *.
   '- (d-fun '_a1 (d-fun '_a2 (d-binop '+ (d-id '_a1) (d-binop '* (d-num -1) (d-id '_a2)))))
   
   ; Writing all of =, >, <=, and >= in terms of <
   '> (d-fun '_a1 (d-fun '_a2 (d-binop '< (d-id '_a2) (d-id '_a1))))
   '= (d-fun '_a1 (d-fun '_a2 (d-if (d-binop '< (d-id '_a1) (d-id '_a2))
                                    *FALSE*
                                    (d-if (d-binop '< (d-id '_a2) (d-id '_a1))
                                          *FALSE*
                                          *TRUE*))))
   '<= (d-fun '_a1 (d-fun '_a2 (d-if (d-binop '< (d-id '_a1) (d-id '_a2))
                                     *TRUE*
                                     ; FIX: (d-id '_a1) (d-id '_a2) => (d-id '_a2) (d-id '_a1)
                                     (d-if (d-binop '< (d-id '_a2) (d-id '_a1))
                                           *FALSE*
                                           *TRUE*))))
   '>= (d-fun '_a1 (d-fun '_a2 (d-if (d-binop '< (d-id '_a1) (d-id '_a2))
                                     *FALSE*
                                     *TRUE*)))))


;; TODO: FIX FOUR ERRORS IN THE DESUGARER (BUT READ NEXT LINES)
;;
;; One of the errors has an additional TODO item below to draw your attention.
;; Another error may seem challenging to fix, but you should be able to fix it
;; using on or the other of two builtin Racket functions if you understand what's
;; going wrong.

;; desugar : SAS -> DAS
;; desugar from the surface syntax to the underlying desugared syntax
;; quite aggressive in this language, e.g., removes empty, empty?, first, and rest.
(define (desugar exp)
  (local [(define (desugar exp)
            (error "Don't call desugar. Call helper instead."))

          (define (helper exp)
            (type-case SAS exp
              [s-num (n) (d-num n)]
              [s-T () (hash-ref *builtins* 'T)]
              [s-F () (hash-ref *builtins* 'F)]
              [s-id (name) (d-id name)]
              [s-binop (op lhs rhs)
                       (if (member op *dbinop*)
                           ; A binop that exists in the desugared language.
                           (d-binop op (helper lhs) (helper rhs))
                           ; A binop that is desugared away.
                           (d-app (d-app (hash-ref *builtins* op)
                                         (helper lhs))
                                  (helper rhs)))]
              [s-bind (bindings body)
                      (foldr (lambda (binding d-body)
                               (type-case SBind binding
                                 [vbinding (name named-exp) (d-recwith name (helper named-exp) d-body)]
                                 [fbinding (fname fparams fbody) (d-recwith fname (helper (s-fun fparams fbody)) d-body)]))
                             (helper body) bindings)]
              [s-fun (names body)
                     (foldr (lambda (name d-body)
                              (d-fun name d-body))
                            (helper body) names)]
              [s-app (fexp aexps)
                     ; FIX: foldr => foldl
                     (foldl (lambda (aexp d-fexp)
                              (d-app (build-type-assertion d-fexp (unTagged) "attempt to apply non-function value") (helper aexp)))
                            (helper fexp) aexps)]
              [s-if (cexp texp eexp)
                    ; FIX: (unTagged) => (boolTag)
                    (d-if (build-type-assertion (helper cexp) (boolTag) "expected a boolean value in condition")
                          (helper texp)
                          (helper eexp))]
              [s-and (exps)
                     (if (empty? exps)
                         (helper (s-T))
                         (helper (s-if (first exps)
                                       (s-and (rest exps))
                                       (s-F))))]
              [s-or (exps)
                    (if (empty? exps)
                        (helper (s-F))
                        (helper (s-if (first exps)
                                      (s-T)
                                      (s-or (rest exps)))))]
              [s-not (exp)
                     ; FIX: d-if => s-if
                     (helper (s-if exp (s-F) (s-T)))]
              [s-bindcc (name body)
                        (d-bindcc name (helper body))]
              [s-begin (exps)
                       ; Note that: (not (empty? exps))
                       (local [(define-values (first-exps last-exp-lst)
                                 (split-at-right exps 1))
                               (define last-exp (first last-exp-lst))]
                         (foldr (lambda (exp d-body)
                                  (d-recwith '_ignore (helper exp) d-body))
                                (helper last-exp) first-exps))]
              [s-set! (name vexp)
                      (d-set! name (helper vexp))]
              [s-is-empty? (exp) (d-app (hash-ref *builtins* 'empty?) (helper exp))]
              
              ; Note that this is NOT a straightforward application of the builtin '_cons
              ; to the two arguments. We have to do a bit more.

              ;; TODO: the most subtle error we introduced is in the s-cons case.
              ;; Fortunately, there's a test case that should make it easy to find and
              ;; fix (if you read carefully!), but can you see how it could cause an
              ;; error at runtime?
              [s-cons (fexp rexp) (d-app (d-app (hash-ref *builtins* '_cons) (helper fexp))
                                         ; FIX: 'ignore => '_ignore
                                         (d-fun '_ignore (helper rexp)))]
              [s-first (exp) (d-app (hash-ref *builtins* 'first) (helper exp))]
              [s-rest (exp) (d-app (hash-ref *builtins* 'rest) (helper exp))]
              [s-empty () (hash-ref *builtins* 'empty)]))]
    (helper exp)))

; Uninteresting cases.
(test (desugar (s-num 1)) (d-num 1))
(test (desugar (s-id 'x)) (d-id 'x))
(test (desugar (s-bindcc 'k (s-num 1))) (d-bindcc 'k (d-num 1)))
(test (desugar (s-set! 'x (s-num 1))) (d-set! 'x (d-num 1)))

; Slightly more interesting because we have to emplace a type check.
(test (desugar (s-if (s-id 'x) (s-id 'y) (s-id 'z)))
      (d-if (build-type-assertion (d-id 'x) (boolTag) "expected a boolean value in condition") (d-id 'y) (d-id 'z)))

; Binops that are NOT desugared away.
(test (desugar (s-binop '+ (s-num 1) (s-id 'y))) (d-binop '+ (d-num 1) (d-id 'y)))
(test (desugar (s-binop '* (s-num 1) (s-id 'y))) (d-binop '* (d-num 1) (d-id 'y)))
(test (desugar (s-binop '/ (s-num 1) (s-id 'y))) (d-binop '/ (d-num 1) (d-id 'y)))
(test (desugar (s-binop '< (s-num 1) (s-id 'y))) (d-binop '< (d-num 1) (d-id 'y)))

; Binops that ARE desugared away.
(test (desugar (s-binop '- (s-num 1) (s-id 'y))) (d-app (d-app (hash-ref *builtins* '-) (d-num 1)) (d-id 'y)))
(test (desugar (s-binop '= (s-num 1) (s-id 'y))) (d-app (d-app (hash-ref *builtins* '=) (d-num 1)) (d-id 'y)))
(test (desugar (s-binop '> (s-num 1) (s-id 'y))) (d-app (d-app (hash-ref *builtins* '>) (d-num 1)) (d-id 'y)))
(test (desugar (s-binop '<= (s-num 1) (s-id 'y))) (d-app (d-app (hash-ref *builtins* '<=) (d-num 1)) (d-id 'y)))
(test (desugar (s-binop '>= (s-num 1) (s-id 'y))) (d-app (d-app (hash-ref *builtins* '>=) (d-num 1)) (d-id 'y)))

; Unrollings: bind, fun, app (which must manage type assertions), begin
(test (desugar (s-bind (list (vbinding 'x (s-num 1))) (s-id 'x)))
      (d-recwith 'x (d-num 1) (d-id 'x)))
(test (desugar (s-bind (list (fbinding 'f '(x) (s-num 1))) (s-id 'x)))
      (d-recwith 'f (d-fun 'x (d-num 1)) (d-id 'x)))
(test (desugar (s-bind (list (vbinding 'x (s-num 1)) (fbinding 'f '(x) (s-num 1))) (s-id 'x)))
      (d-recwith 'x (d-num 1) (d-recwith 'f (d-fun 'x (d-num 1)) (d-id 'x))))
(test (desugar (s-bind empty (s-num 1)))
      (d-num 1))

(test (desugar (s-fun '(x) (s-num 2))) (d-fun 'x (d-num 2)))
(test (desugar (s-fun '(x y z) (s-num 1))) (d-fun 'x (d-fun 'y (d-fun 'z (d-num 1)))))

(test (desugar (s-app (s-id 'f) (list (s-id 'a))))
      (d-app (build-type-assertion (d-id 'f) (unTagged) "attempt to apply non-function value") (d-id 'a)))
(test (desugar (s-app (s-id 'f) (list (s-id 'a) (s-id 'b) (s-id 'c))))
      (d-app (build-type-assertion
              (d-app (build-type-assertion (d-app (build-type-assertion (d-id 'f)
                                                                        (unTagged) "attempt to apply non-function value")
                                                  (d-id 'a))
                                           (unTagged) "attempt to apply non-function value")
                     (d-id 'b))
              (unTagged) "attempt to apply non-function value")
             (d-id 'c)))

(test (desugar (s-begin (list (s-id 'x))))
      (d-id 'x))
(test (desugar (s-begin (list (s-id 'x) (s-id 'y) (s-id 'z))))
      (d-recwith '_ignore (d-id 'x)
                 (d-recwith '_ignore (d-id 'y)
                            (d-id 'z))))



; Booleans
(test (desugar (s-T)) (hash-ref *builtins* 'T))
(test (desugar (s-F)) (hash-ref *builtins* 'F))
(test (desugar (s-and empty)) (hash-ref *builtins* 'T))
(test (desugar (s-and (list (s-F))))
      (desugar (s-if (s-F) (s-T) (s-F))))
(test (desugar (s-and (list (s-id 'x) (s-id 'y))))
      (desugar (s-if (s-id 'x)
                     (s-and (list (s-id 'y)))
                     (s-F))))
(test (desugar (s-and (list (s-id 'x) (s-id 'y) (s-id 'z))))
      (desugar (s-if (s-id 'x)
                     (s-and (list (s-id 'y) (s-id 'z)))
                     (s-F))))

(test (desugar (s-or empty)) (hash-ref *builtins* 'F))
(test (desugar (s-or (list (s-id 'x))))
      (desugar (s-if (s-id 'x) (s-T) (s-F))))
(test (desugar (s-or (list (s-id 'x) (s-id 'y))))
      (desugar (s-if (s-id 'x)
                     (s-T)
                     (s-or (list (s-id 'y))))))
(test (desugar (s-or (list (s-id 'x) (s-id 'y) (s-id 'z))))
      (desugar (s-if (s-id 'x)
                     (s-T)
                     (s-or (list (s-id 'y) (s-id 'z))))))

(test (desugar (s-not (s-id 'x)))
      (desugar (s-if (s-id 'x)
                     (s-F)
                     (s-T))))



; Lists
(test (desugar (s-empty)) (hash-ref *builtins* 'empty))
(test (desugar (s-is-empty? (s-id 'x))) (d-app (hash-ref *builtins* 'empty?) (d-id 'x)))
(test (desugar (s-cons (s-id 'x) (s-id 'y)))
      ; cons itself roughly translates to (fun (a) (fun (b) (fun (selector) (selector a b))))
      ; then, we deal with the deferred evaluatino of b and the immediate necessity to apply to
      ; the given expressions, and tagging!
      (d-app
       (d-app
        ; This is the cons function:
        (d-fun '_a
               (d-fun '_b_thunk
                      (d-tag (seqTag)
                             (d-fun '_selector (d-app (d-app (d-id '_selector)
                                                             (d-id '_a))
                                                      ; We don't yet run the thunk.
                                                      (d-id '_b_thunk))))))
        ; apply to first argument:
        (d-id 'x))
       ; apply to thunked second argument:
       (d-fun '_ignore (d-id 'y))))
(test (desugar (s-first (s-id 'x)))
      (d-app (hash-ref *builtins* 'first) (d-id 'x)))
(test (desugar (s-rest (s-id 'x)))
      (d-app (hash-ref *builtins* 'rest) (d-id 'x)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; INTERPRETATION ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The environment associates variable names with their memory locations.
(define-type Env
  [mtEnv]
  [anEnv (name symbol?) 
         (locn integer?) 
         (rest Env?)])

;; The store associates memory locations with their values.
(define-type Store 
  [mtStore]
  [aStore (locn integer?) 
          (val Value?) 
          (more-store Store?)])



;; lookup-env : symbol Env -> integer
;; given a name and an environment, produces the (first) location associated
;; with that name in the environment or an error otherwise
(define (lookup-env name env)
  (type-case Env env
    [mtEnv () (error 'lookup "free identifier ~a" name)]
    [anEnv (bound-name bound-value rest-env)
           (cond [(not (symbol=? bound-name name)) (lookup-env name rest-env)]
                 [else bound-value])]))


;; lookup-store : integer Store -> D-CFAE-Value
;; Finds the value at location locn in store or errors if it is undefined
(define (lookup-store locn store)
  (local [(define (lookup-helper locn store)
            (type-case Store store
              [mtStore () (error 'lookup-store "unallocated memory location ~a" locn)]
              [aStore (alloc-locn alloc-value rest-store)
                      (if (= alloc-locn locn)
                          alloc-value
                          (lookup-helper locn rest-store))]))]
    (lookup-helper locn store)))

;; lookup : symbol Env Store -> Value
;; looks up the value associated with name via the environment and then the store.
;; Note: produces an error if it looks up anything with the error tag.
(define (lookup name env store)
  (local [(define value (lookup-store (lookup-env name env) store))]
    (if (errorTag? (get-value-tag value))
        (error 'lookup "reference to uninitialized variable ~a" name)
        value)))

;; get-next-memory-location : Store -> integer
;; produce a value one larger than the largest store address used so far
;; or if the store is empty, produce 1
(define (get-next-memory-location store)
  (type-case Store store
    [mtStore () 1]
    [aStore (alloc-locn alloc-value rest-store)
            (max (+ alloc-locn 1)
                 (get-next-memory-location rest-store))]))



(test/exn (lookup-env 'x (mtEnv)) "")
(test (lookup-env 'x (anEnv 'x 1 (mtEnv))) 1)
(test/exn (lookup-env 'y (anEnv 'x 1 (mtEnv))) "")
(test (lookup-env 'x (anEnv 'x 1
                            (anEnv 'y 2 (mtEnv)))) 1)
(test (lookup-env 'y (anEnv 'x 1
                            (anEnv 'y 2 (mtEnv)))) 2)
(test (lookup-env 'x (anEnv 'x 1
                            (anEnv 'x 2 (mtEnv)))) 1)

(test/exn (lookup-store 1 (mtStore)) "")
(test (lookup-store 1 (aStore 1 (numV 1) (mtStore))) (numV 1))
(test/exn (lookup-store 2 (aStore 1 (numV 1) (mtStore))) "")
(test (lookup-store 1 (aStore 1 (numV 1)
                              (aStore 2 (numV 2) (mtStore)))) (numV 1))
(test (lookup-store 2 (aStore 1 (numV 1)
                              (aStore 2 (numV 2) (mtStore)))) (numV 2))
(test (lookup-store 1 (aStore 1 (numV 1)
                              (aStore 1 (numV 2) (mtStore)))) (numV 1))

(test (lookup 'x (anEnv 'x 3 (mtEnv)) (aStore 3 (numV 1) (mtStore))) (numV 1))
(test/exn (lookup 'x (anEnv 'x 1 (mtEnv)) (aStore 1 *ERROR_VALUE* (mtStore))) "")




;; TODO: FIX THREE ERRORS IN THE INTERPRETER

;; interp/k : SAS Env Store (Value Store -> ()) -> ()
;; Given a desugared expression exp, environment env, store sto,
;; and continuation (of two arguments, a value and a store),
;; evaluates exp and passes it and the newly generated store to
;; k. Does not return, assuming k is indeed a continuation rather
;; than a normal function.
(define (interp/k exp env sto k)
  (local [;; runs the Racket operations corresponding to the given symbol,
          ;; in continuation passing style and managing wrapping/unwrapping
          ;; values.
          (define (run-binop/k op-symbol lval rval sto k)
            (when (not (numV? lval))
              (error op-symbol "attempt to add a non-numeric value ~a" (gloss lval)))
            (when (not (numV? rval))
              (error op-symbol "attempt to add a non-numeric value ~a" (gloss rval)))
            (local [(define result ((eval op-symbol (make-base-namespace)) (numV-n lval) (numV-n rval)))]
              (cond [(number? result) ;FIX: wrap it with continuation
                     (k (numV result) sto)]
                    [(boolean? result) (interp/k (hash-ref *builtins* (if result 'T 'F)) (mtEnv) sto k)]
                    [else (error op-symbol "produced a value of unexpected type (not numeric or boolean): ~a" result)])))] 
    (type-case DAS exp
      [d-tag (vt exp)
             (interp/k exp env sto
                       (lambda (it sto)
                         (type-case Value it
                           [numV (n) (error 'interp/k "cannot tag a number with a type: ~a" (gloss it))]
                           [closureV (old-vt proc)
                                     (k (closureV vt proc) sto)])))]
      [d-check (vt exp)
               (interp/k exp env sto
                         (lambda (it sto)
                           (interp/k (hash-ref *builtins*
                                               ; FIX: 'F 'T => 'T 'F
                                               (if (equal? vt (get-value-tag it)) 'T 'F))
                                     env sto k)))]
      [d-assert (vt text exp)
                (interp/k exp env sto
                          (lambda (it sto)
                            (if (equal? vt (get-value-tag it))
                                (k it sto)
                                (error 'assert "~a produced the value ~a, which is not of type ~a. ~a"
                                       exp (gloss it sto) vt text))))]  
      [d-num (n) (k (numV n) sto)]
      [d-id (name) (k (lookup name env sto) sto)]
      [d-binop (op lexp rexp)
               (interp/k lexp env sto
                         (lambda (l-it sto)
                           (interp/k rexp env sto
                                     (lambda (r-it sto)
                                       (run-binop/k op l-it r-it sto k)))))]
      [d-recwith (name named-expr body)
                 (local [(define new-loc (get-next-memory-location sto))
                         (define new-env (anEnv name new-loc env))
                         (define new-sto (aStore new-loc *ERROR_VALUE* sto))]
                   (interp/k named-expr new-env new-sto
                             (lambda (it sto)
                               ; Establish the circular reference.
                               (interp/k body new-env (aStore new-loc it sto) k))))]
      [d-fun (name body)
             (k (closureV (unTagged)
                          (lambda (v sto otherk)
                            (local [(define new-loc (get-next-memory-location sto))]
                              (interp/k body (anEnv name new-loc env) (aStore new-loc v sto) otherk)))) sto)]
      [d-app (fexp aexp)
             (interp/k fexp env sto
                       (lambda (f-it sto)
                         (if (closureV? f-it)
                             (interp/k aexp env sto
                                       (lambda (a-it sto)
                                         ((closureV-proc f-it)
                                          a-it sto k)))
                             (error 'interp/k "attempt to apply a non-function value ~a from ~a" (gloss f-it sto) fexp))))]
      [d-if (cexp texp eexp)
            ; Need to:
            ; (1) evaluate the cexp
            ; (2) apply the boolean to thunked versions of texp and eexp
            (interp/k (d-app (d-app cexp
                                    (d-fun '_ignore texp))
                             (d-fun '_ignore eexp))
                      env sto k)]
      [d-bindcc (name body)
                (local [(define cont-as-clos
                          (closureV (unTagged)
                                    ; Build a function that when later invoked will..
                                    (lambda (v sto otherk)
                                      ; ..discard the continuation current at the time this
                                      ; lambda is called and jump back to the one current at
                                      ; the time the lambda is being created instead. BUT,
                                      ; maintain the store from the time the lambda is called.
                                      ; FIX: implement the continuation
                                      (k v sto))))
                        (define new-loc (get-next-memory-location sto))]
                  (interp/k body (anEnv name new-loc env) (aStore new-loc cont-as-clos sto) k))]
      [d-set! (name vexp)
              (interp/k vexp env sto
                        (lambda (it sto)
                          (k it (aStore (lookup-env name env) it sto))))])))
  

;; gloss : Value Store -> (or number internal-procedure-representation boolean list)
;; glosses (renders for easy reading) the internal value v
;; procedures are hard to render; so, they're left as procedures.
;; CAUTION: gloss does not understand how to thread store updates.
;; WE PROMISE TO ASK NOTHING ABOUT THIS HIDEOUS FUNCTION ON THE EXAM!
(define (gloss v sto)
  (local [(define (gloss v sto)
            (error "call helper/k, not gloss"))
          
          (define (numV->bool v)
            (not (zero? (numV-n v))))
          (define (build-thunk n)
            (closureV (unTagged) (lambda (ignore sto k) (k (numV n) sto))))
          (define seq-unroll-closureV
            ; Build a closure that acts as the selector argument to a cons/seq
            ; cell and "unrolls" that into a Racket list.
            (closureV (unTagged)
                      ; Given the value of first..
                      (lambda (fst sto k)
                        ; Call the continuation on a closure awaiting the rest thunk..
                        (k (closureV (unTagged)
                                     (lambda (rst-t sto k)
                                       ; ..which then applies the rst-t thunk
                                       ((closureV-proc rst-t)
                                        (numV 0)
                                        sto
                                        (lambda (rst sto)
                                          ; And then starts glossing the pieces it gets,
                                          ; starting with first..
                                          (helper/k
                                           fst sto
                                           (lambda (g-fst sto)
                                             ; Then rest..
                                             (helper/k
                                              rst sto
                                              (lambda (g-rst sto)
                                                ; And finally gives back the result.
                                                (k (cons g-fst g-rst) sto)))))))))
                           sto))))

          ; we will intentionally have v sometimes be a Value and sometimes be a Racket value.
          (define (helper/k v sto k)
            (type-case Value v
              [numV (n) (k n sto)]
              [closureV (vt proc)
                        (type-case ValueTag vt
                          [unTagged () (k proc sto)]
                          [boolTag ()
                                   (proc (build-thunk 1)
                                         sto
                                         (lambda (it sto)
                                           ((closureV-proc it)
                                            (build-thunk 0)
                                            sto
                                            (lambda (nv sto) (k (numV->bool nv) sto)))))]
                          [seqTag ()
                                  (proc seq-unroll-closureV sto k)]
                          [emptyTag () (k empty sto)]
                          [errorTag () (k 'ERROR sto)])]))]
    (let/cc k
      (begin
        (helper/k v sto (lambda (v sto) (k v)))
        (error "helper/k returned inside gloss. oops!")))))

(test (gloss (numV 1) (mtStore)) 1)
(test (call/cc (curry (gloss (closureV (unTagged) (lambda (x k) (k 'SUCCESS))) (mtStore)) (numV 1)))
      'SUCCESS)
(test (call/cc (curry (gloss (closureV (unTagged) (lambda (x k) (k x))) (mtStore)) (numV 1)))
      (numV 1))

; It's challenging to test gloss without running code beyond simple examples like these.
; So, we leave the rest of the testing to run.



;; run : sexpression -> glossed value
;; Given a program, produces the glossed value of that program.
;; (So, e.g., a Racket boolean like true or false rather than an
;; internal language representation.)
(define (run sexp)
  (let/cc k 
    (begin
      (interp/k (desugar (parse sexp)) (mtEnv) (mtStore)
                (lambda (v sto) (k (gloss v sto))))
      (error "interp returned, which is an ERROR!"))))

(test (run 'T) true)
(test (run 'F) false)
(test (run 'empty) empty)
(test (run '{cons 1 empty}) '(1))
(test (run '{cons 1 {cons 2 empty}}) '(1 2))



  




;;;;;;;;;;;; INTEGRATION TESTS ;;;;;;;;;;;;;;;;;;;



; numbers
(test (run 1) 1)
(test (run 2) 2)

; numeric binops
(test (run '{+ 1 2}) 3)
(test (run '{* 1 2}) 2)
(test (run '{- 1 2}) -1)
(test (run '{/ 1 2}) 1/2)

; basic boolean values
(test (run 'T) true)
(test (run 'F) false)
(test/exn (run '{T 1}) "")
(test/exn (run '{F 1}) "")

; comparison binops
(test (run '{< 1 2}) true)
(test (run '{< 2 2}) false)
(test (run '{< 3 2}) false)
(test (run '{= 1 2}) false)
(test (run '{= 2 2}) true)
(test (run '{= 3 2}) false)
(test (run '{> 1 2}) false)
(test (run '{> 2 2}) false)
(test (run '{> 3 2}) true)
(test (run '{<= 1 2}) true)
(test (run '{<= 2 2}) true)
(test (run '{<= 3 2}) false)
(test (run '{>= 1 2}) false)
(test (run '{>= 2 2}) true)
(test (run '{>= 3 2}) true)

; bindings
(test (run '{bind {{define x 1}}
                  x})
      1)
(test (run '{bind {{define x 1}}
                  2})
      2)
(test (run '{bind {{define {f x} {+ x 1}}}
                  {f 1}})
      2)
(test (run '{bind {{define {f x} {+ x 1}}}
                  1})
      1)
(test (run '{bind {{define {fact n}
                     {if {= n 0}
                         1
                         {* n {fact {- n 1}}}}}}
                  {fact 6}})
      720)
(test (run '{bind {{define x 1}}
                  {bind {{define x 2}}
                        x}})
      2)
(test (run '{bind {{define x 1}
                   {define x 2}}
                  x})
      2)
(test (run '{bind {{define x 1}
                   {define y 2}}
                  {+ x y}})
      3)
(test/exn (run 'x) "")
(test/exn (run '{bind {{define x 1}} y}) "")
(test/exn (run '{bind {{define x x}} 1}) "")

; functions and application
(test (run '{{fun {x} x} 1}) 1)
(test (run '{{fun {x y z} x} 1 2 3}) 1)
(test (run '{{fun {x y z} y} 1 2 3}) 2)
(test (run '{{fun {x y z} z} 1 2 3}) 3)
(test/pred (run '{{fun {x y z} z} 1 2})
           procedure?)
(test/exn (run '{{fun {x} x} 1 2}) "")

; scope check
(test (run '{bind {{define y 1}
                   {define x 10}
                   {define {f y} {+ x y}}
                   {define x 100}}
                  {f 1000}})
      1010)

; currying
(test (run '{bind {{define {add x y} {+ x y}}
                   {define plus2 {add 2}}}
                  {plus2 10}})
      12)

; conditionals, including testing deferred evaluation/short-circuiting.
(test (run '{if T 1 {1 2}}) 1)
(test (run '{if F {1 2} 1}) 1)
(test/exn (run '{if F 1 {1 2}}) "")
(test/exn (run '{if T {1 2} 1}) "")
(test/exn (run '{if {fun {x-thunk} {fun {y-thunk} {x-thunk x-thunk}}} 1 2}) "")

(test (run '{and}) true)
(test (run '{and T}) true)
(test (run '{and F}) false)
(test (run '{and T T}) true)
(test (run '{and F T}) false)
(test (run '{and T F}) false)
(test (run '{and F {1 2}}) false)
(test/exn (run '{and 1}) "")
(test/exn (run '{and T {1 2}}) "")

(test (run '{or}) false)
(test (run '{or T}) true)
(test (run '{or F}) false)
(test (run '{or F F}) false)
(test (run '{or F T}) true)
(test (run '{or T F}) true)
(test (run '{or T {1 2}}) true)
(test/exn (run '{or 1}) "")
(test/exn (run '{or F {1 2}}) "")

(test (run '{not T}) false)
(test (run '{not F}) true)
(test/exn (run '{not 1}) "")
(test/exn (run '{not {fun {x-thunk} {fun {y-thunk} {x-thunk x-thunk}}}}) "")

; lists
(test (run 'empty) empty)
(test (run '{cons 1 empty}) '(1))
(test (run '{cons 1 {cons 2 empty}}) '(1 2))
(test (run '{cons {cons 1 2} {cons 3 4}}) (cons (cons 1 2) (cons 3 4)))
(test (run '{empty? empty}) true)
(test (run '{empty? {cons 1 2}}) false)
(test (run '{empty? 1}) false)
(test (run '{first {cons 1 2}}) 1)
(test (run '{rest {cons 1 2}}) 2)
(test (run '{bind {{define ones {cons 1 ones}}}
                  {first ones}})
      1)
(test (run '{bind {{define ones {cons 1 ones}}}
                  {first {rest ones}}})
      1)
(test (run '{bind {{define {inf-zip-+ l1 l2} {cons {+ {first l1} {first l2}}
                                                   {inf-zip-+ {rest l1} {rest l2}}}}
                   {define ones {cons 1 ones}}
                   {define nats {cons 1 {inf-zip-+ ones nats}}}
                   {define fibs {cons 1 {cons 1 {inf-zip-+ fibs {rest fibs}}}}}
                   {define {nth n lst}
                     {if {= n 0} {first lst} {nth {- n 1} {rest lst}}}}}
                  {nth 9 ones}})
      1)
(test (run '{bind {{define {inf-zip-+ l1 l2} {cons {+ {first l1} {first l2}}
                                                   {inf-zip-+ {rest l1} {rest l2}}}}
                   {define ones {cons 1 ones}}
                   {define nats {cons 1 {inf-zip-+ ones nats}}}
                   {define fibs {cons 1 {cons 1 {inf-zip-+ fibs {rest fibs}}}}}
                   {define {nth n lst}
                     {if {= n 0} {first lst} {nth {- n 1} {rest lst}}}}}
                  {nth 9 nats}})
      10)
(test (run '{bind {{define {inf-zip-+ l1 l2} {cons {+ {first l1} {first l2}}
                                                   {inf-zip-+ {rest l1} {rest l2}}}}
                   {define ones {cons 1 ones}}
                   {define nats {cons 1 {inf-zip-+ ones nats}}}
                   {define fibs {cons 1 {cons 1 {inf-zip-+ fibs {rest fibs}}}}}
                   {define {nth n lst}
                     {if {= n 0} {first lst} {nth {- n 1} {rest lst}}}}}
                  {nth 5 fibs}})
      8)
(test (run '{bind {{define {inf-zip-+ l1 l2} {cons {+ {first l1} {first l2}}
                                                   {inf-zip-+ {rest l1} {rest l2}}}}
                   {define ones {cons 1 ones}}
                   {define nats {cons 1 {inf-zip-+ ones nats}}}
                   {define fibs {cons 1 {cons 1 {inf-zip-+ fibs {rest fibs}}}}}
                   {define {nth n lst}
                     {if {= n 0} {first lst} {nth {- n 1} {rest lst}}}}}
                  {nth 9 fibs}})
      55)
(test/exn (run '{first 1}) "")
(test/exn (run '{first {fun {selector} {selector 1 2}}}) "")
(test/exn (run '{rest 1}) "")
(test/exn (run '{rest {fun {selector} {selector 1 2}}}) "")

; Continuations!
(test (run '{+ 4 {bindcc k 5}}) 9)
(test (run '{+ 4 {bindcc k {k 5}}}) 9)
(test (run '{+ 4 {bindcc k {k 2}}}) 6)
(test (run '{+ 4 {bindcc k {+ 1000 {k 2}}}}) 6)
(test (run '{+ {bindcc k {k 3}} 1}) 4)

(test (run '{bindcc k {and T {k 3} F}}) 3)
(test (run '{bindcc k 3}) 3)

; begin WITHOUT state
(test (run '{begin 1}) 1)
(test (run '{begin 1 2}) 2)
(test/exn (run '{begin {1 2} 2}) "") ; error even if throwing the value away
(test (run '{bindcc k {begin {k 1} 2}}) 1) ; too much fun to escape a begin!


; State requires extensive testing.

; First, the basics.
(test (run '{bind {{define x 1}}
                  {set! x 2}})
      2)
(test (run '{bind {{define x 1}}
                  {begin
                    {set! x 2}
                    x}})
      2)
(test (run '{bind {{define x 1}
                   {define y 10}}
                  {begin
                    {set! x 2}
                    {+ x y}}})
      12)
(test (run '{bind {{define x 1}
                   {define y 10}}
                  {begin
                    {set! x {+ x 1}}
                    {+ x y}}})
      12)
(test (run '{bind {{define x 1}
                   {define y 10}}
                  {begin
                    {set! x {+ x 1}}
                    {set! y {* x y}}
                    {+ x y}}})
      22)

; Now, on to detailed checks of store threading, construct by constuct.
; To help with that, here's some support code. It wraps an sexp in a
; definition for x and inserts mutations to x wherever it finds a
; designated placeholder.
(define (build-test placeholder sexp)
  (local [(define i 0)
          (define (replacement)
            (begin (set! i (add1 i))
                   `{* ,i {set! x {* x 10}}}))
          (define (traverse sexp)
            (cond [(cons? sexp)
                   (cons (traverse (car sexp))
                         (traverse (cdr sexp)))]
                  [(equal? sexp placeholder)
                   (replacement)]
                  [else sexp]))]
    `{bind {{define x 1}}
           ,(traverse sexp)}))


; Binops
(test (run (build-test '_ '{+ _ _})) 210)
(test (run (build-test '_ '{+ _ {+ {+ _ _} _}})) 43210) ; store before and after binop are both good
(test (run (build-test '_ '{- _ _})) (- 10 200))
(test (run (build-test '_ '{+ _ {+ {- _ _} _}})) (+ 10 (- 200 3000) 40000))
(test (run (build-test '_ '{* _ _})) (* 10 200))
(test (run (build-test '_ '{+ _ {+ {* _ _} _}})) (+ 10 (* 200 3000) 40000))
(test (run (build-test '_ '{/ _ _})) (/ 10 200))
(test (run (build-test '_ '{+ _ {+ {/ _ _} _}})) (+ 10 (/ 200 3000) 40000))
(test (run (build-test '_ '{< _ _})) true)
(test (run (build-test '_ '{< {* 20 _} _})) false)
(test (run (build-test '_ '{+ _ {+ {begin {< _ _} 0} _}})) (+ 10 40000))
(test (run (build-test '_ '{= _ _})) false)
(test (run (build-test '_ '{= {* 20 _} _})) true)
(test (run (build-test '_ '{+ _ {+ {begin {= _ _} 0} _}})) (+ 10 40000))
(test (run (build-test '_ '{>= _ _})) false)
(test (run (build-test '_ '{>= {* 20 _} _})) true)
(test (run (build-test '_ '{+ _ {+ {begin {>= _ _} 0} _}})) (+ 10 40000))
(test (run (build-test '_ '{<= _ _})) true)
(test (run (build-test '_ '{= {* 21 _} _})) false)
(test (run (build-test '_ '{+ _ {+ {begin {<= _ _} 0} _}})) (+ 10 40000))

(test (run (build-test '_ '{bind {{define y _}}
                                 {+ _ y}}))
      210)
(test (run (build-test '_ '{bind {{define {f y} {+ _ y}}}
                                 {+ _ {+ {f _} {f _}}}}))
      (+ 20 1000 300 100000 40000))
(test (run (build-test '_ '{+ _
                              {+ {bind {{define y _}}
                                       {+ y _}} _}}))
      (+ 10 200 3000 40000))
(test (run (build-test '_ '{bind {{define y _}
                                  {define z _}
                                  {define {f w} {+ w _}}
                                  {define q _}}
                                 {+ y {+ z {+ q {+ {f _} _}}}}}))
      (+ 10 200 4000 300000 50000 6000000))

; Functions and application (largely tested above already!).
(test (run (build-test '_ '{begin {fun {x y z} _}
                                  _}))
      20)
(test (run (build-test '_ '{{fun {x1 y z} {+ _ {+ x1 {+ y z}}}} _ _ _}))
      (+ 10000 20 300 4000))
(test (run (build-test '_ '{{{fun {x1 y z} {+ _ {+ x1 {+ y z}}}} _ _}
                            _}))
      (+ 10000 20 300 4000))

; Conditionals and booleans
(test (run (build-test '_ '{+ _ {+ {if {= _ 200}
                                       {+ _ 1}
                                       _} _}}))
      (+ 10 3000 1 50000))
(test (run (build-test '_ '{+ _ {+ {if {= _ 100}
                                       {+ _ 1}
                                       _} _}}))
      (+ 10 4000 50000))
(test (run (build-test '_ '{if {and {= _ 10} {= _ 200} {= _ 3000}}
                               _
                               {+ 1 _}}))
      40000)
(test (run (build-test '_ '{if {not {or {not {= _ 10}} {not {= _ 200}} {not {= _ 3000}}}}
                               _
                               {+ 1 _}}))
      40000)

; set! and begin
(test (run (build-test '_ '{bind {{define y 2}}
                                 {+ _ {+ {set! y {+ y _}} {+ y _}}}}))
      (+ 10 202 202 3000))
(test (run (build-test '_ '{+ _ {+ {begin _ _ _} _}}))
      (+ 10 40000 500000))

; list operations
(test (run (build-test '_ '{+ _ {if {empty? {if {= _ 200} empty {cons 1 empty}}} _ {+ _ 1}}}))
      (+ 10 3000))
(test (run (build-test '_ '{+ _ {if {empty? {if {< _ 200} empty {cons 1 empty}}} _ {+ _ 1}}}))
      (+ 10 4000 1))
(test (run (build-test '_ '{+ _ {bind {{define pair {cons _ _}}}
                                      {+ {first pair}
                                         {rest pair}}}}))
      (+ 10 200 3000))

; This test behaves (perhaps) slightly surprisingly. The rest expression
; is never accessed and so never evaluated, under our deferred-evaluation
; semantics.
(test (run (build-test '_ '{+ _ {+ {first {begin _ {cons _ _}}} _}}))
      (+ 10 3000 50000))

(test (run (build-test '_ '{+ _ {+ {rest {begin _ {cons 2 _}}} _}}))
      (+ 10 3000 40000))

(test (run (build-test '_ '{+ _ {+ {bindcc k _} _}}))
      (+ 10 200 3000))
(test (run (build-test '_ '{+ {bindcc k {begin _ {k _} _}} _}))
      (+ 200 4000))

