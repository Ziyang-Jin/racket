;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname Ass24) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
;; Exercise 1

;; helper 1
;; element list -> list
(define (create-list e1 l2)
  (map (lambda (e2)
         (list e1 e2))
       l2))

(check-expect (create-list 1 '(2 3))
              '((1 2) (1 3)))

;; helper 2
;; list list -> list
(define (cartesian-product-2 l1 l2)
  (if (empty? l1)
      '()
      (append (create-list (first l1) l2) (cartesian-product-2 (rest l1) l2))))

(check-expect (cartesian-product-2 '(0 1 2) '(3 4))
              '((0 3) (0 4) (1 3) (1 4) (2 3) (2 4)))

;; helper 3
(define (generate-list-helper l1 l2)
  (map (λ (e2)
         (append l1 (list e2)))
       l2))
(check-expect (generate-list-helper '(1) '(2 3)) '((1 2) (1 3)))

;; helper 4
;; list-of-list list -> list-of-list
(define (generate-list ll l)
  (if (empty? ll)
      '()
      (append (generate-list-helper (first ll) l) (generate-list (rest ll) l))))

(check-expect (generate-list '((1 2) (3 4)) '(5 6))
              '((1 2 5)
                (1 2 6)
                (3 4 5)
                (3 4 6)))

;; helper 5
;; list list -> list
;; rsf (rest of the list) -> result
(define (cartesian-product-helper rsf l)
  (if (empty? l)
      rsf
      (cartesian-product-helper (generate-list rsf (first l)) (rest l))))

(check-expect (cartesian-product-helper '((1 2) (3 4)) '((5 6)))
              '((1 2 5)
                (1 2 6)
                (3 4 5)
                (3 4 6)))

;;
(define (cartesian-product l)
  (cond
    [(empty? l) '()]
    [(equal? (length l) 1) (list (first l))]
    [else (cartesian-product-helper (cartesian-product-2 (first l) (second l)) (rest (rest l)))]))

(check-expect (cartesian-product '((0 1 2) (3 4)))
              '((0 3) (0 4) (1 3) (1 4) (2 3) (2 4)))

(check-expect (cartesian-product '((1 2 3)))
              '((1 2 3)))

(check-expect (cartesian-product '((1) (2) (3)))
              '((1 2 3)))

(check-expect (cartesian-product '((1 2) (3 4) (5 6)))
              '((1 3 5)
                (1 3 6)
                (1 4 5)
                (1 4 6)
                (2 3 5)
                (2 3 6)
                (2 4 5)
                (2 4 6)))

(check-expect (cartesian-product '((a b) (red green blue) (hutt putt)))
              '((a red hutt)
                (a red putt)
                (a green hutt)
                (a green putt)
                (a blue hutt)
                (a blue putt)
                (b red hutt)
                (b red putt)
                (b green hutt)
                (b green putt)
                (b blue hutt)
                (b blue putt)))

