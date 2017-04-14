;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname Ass17) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
; An Sexpr is one of:
; - Symbol
; - Lexpr

; A Lexpr is one of:
; - '()
; - (cons Sexpr Lexpr)

; A [Maybe X] is one of:
; - #false
; - X

; Exercise 1
(define (traverse sexpr path)
  (cond [(equal? (length path) 0) sexpr]
        [(> (first path) (sub1 (length sexpr))) #false]
        [else (traverse (list-ref sexpr (first path)) (rest path))]))

(define t-sexpr '((a (b (c d e) f g) h i)) )
(define t-path '(0 1 1 2))
(define t-path-2 '(3 1 1 9))

(check-expect (traverse t-sexpr t-path) 'e)
(check-expect (traverse t-sexpr t-path-2) #false)


; Exercise 2
(define (find-path sexpr symbl)
  (cond [(equal? sexpr symbl) '()]
        [(not (list? sexpr)) #false]
        [else (check-it-boy sexpr symbl 0)]))

(define (check-it-boy sexpr symbl i)
  (cond [(>= i (length sexpr)) #false]
        [(equal? (list-ref sexpr i) symbl) (list i)]
        [(not (equal? #false (find-path (list-ref sexpr i) symbl))) (cons i (find-path (list-ref sexpr i) symbl))]
        [else (check-it-boy sexpr symbl (add1 i))]))

(check-expect (find-path t-sexpr 'b) '(0 1 0))
(check-expect (find-path t-sexpr 'z) #false)

; Exercise 3

; definitions
(define-struct leaf [])
(define-struct node [data left right])
(define-struct person [name yob])

; solution
(define (oldest ft)
  (cond [(equal? ft (make-leaf )) #false]
        [else
         (cond [(and (not (equal? #false (oldest (node-left ft)))) (not (equal? #false (oldest (node-right ft))))) (who-is-oldest (node-data ft) (oldest (node-left ft)) (oldest (node-right ft)))]
               [(not (equal? #false (oldest (node-left ft)))) (who-is-older (node-data ft) (oldest (node-left ft)))]
               [(not (equal? #false (oldest (node-right ft)))) (who-is-older (node-data ft) (oldest (node-right ft)))]
               [else (node-data ft)])]))

(define (who-is-oldest p1 p2 p3)
  (cond [(and (< (person-yob p1) (person-yob p2)) (< (person-yob p1) (person-yob p3))) p1]
        [(and (< (person-yob p2) (person-yob p1)) (< (person-yob p2) (person-yob p3))) p2]
        [else p3]))

(define (who-is-older p1 p2)
  (cond [(< (person-yob p1) (person-yob p2)) p1]
        [else p2]))

;examples
(define ft1 (make-leaf ))
(define ft2 (make-node (make-person "Jack" 1999)
                       ft1
                       ft1))
(define ft3 (make-node
             (make-person "Lamn" 1990)
             (make-node (make-person "Linda" 1970)
                        (make-node
                         (make-person "Cindy" 1950)
                         ft1
                         ft1)
                        (make-node
                         (make-person "Harry" 1945)
                         ft1
                         ft1))
             (make-node (make-person "Parker" 1965)
                        (make-node
                         (make-person "Dora" 1945)
                         ft1
                         ft1)
                        (make-node
                         (make-person "Sumail" 1940)
                         ft1
                         ft1))))

(check-expect (oldest ft1) #false)
(check-expect (oldest ft2) (node-data ft2))
(check-expect (oldest ft3) (make-person "Sumail" 1940))