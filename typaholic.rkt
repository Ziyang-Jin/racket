;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname typaholic) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(require 2htdp/universe)
(require 2htdp/image)

(define GRID-HEIGHT 40)
(define GRID-WIDTH 40)
(define CELL-HEIGHT 15)
(define CELL-WIDTH 15)
(define ACTIVE-COLOR "green")
(define TYPING-COLOR "purple")
(define STUCK-COLOR "red")
(define SCENE-HEIGHT (* GRID-HEIGHT CELL-HEIGHT))
(define SCENE-WIDTH (* GRID-WIDTH CELL-WIDTH))
(define SCENE (empty-scene SCENE-WIDTH SCENE-HEIGHT))


(define-struct word-obj (word posn is-active))
; A Word Object is (make-wordObj String Position Boolean)

(define-struct world (lowo input))
; A World is (make-world list of wordObj String)

(define dot (make-posn 0 0))

(define init-word-obj (make-word-obj "Start" dot true))
(define init-word-list '())
(define init-input "")
(define init-world (make-world init-word-list init-input))

(define DICTIONARY (list "alan" "perlis" "maurice" "wilkes" "richard" "hamming" "marvin" "minsky" "john" "mccarthy" "donald" "knuth" "herbert" "simon" "bob" "floyd" "tony" "hoare" "edgar" "codd"))

;; (list of String) -> String
(define (choose-random-word dic)
  (list-ref dic (random (- (length dic) 1))))
;; generate a new word object
(define (generate-new-word-obj x)
  (make-word-obj (choose-random-word DICTIONARY) (make-posn (* (random GRID-WIDTH) CELL-WIDTH) 0) true))
;; (int)y -> (int)y
(define (new-y y)
      (+ y CELL-HEIGHT))
;; Position -> Position
(define (new-posn p)
  (make-posn (posn-x p) (new-y (posn-y p))))
;; WordObject -> (int)y
(define (get-y wo)
  (posn-y (word-obj-posn wo)))
;; WordObject -> (int)x
(define (get-x wo)
  (posn-x (word-obj-posn wo)))

;; WordObject (listof WordObject) -> WordObject
(define (update-word-obj wo lowo)
  (if (and
       (< (get-y wo) (* (- GRID-HEIGHT 1) CELL-HEIGHT))
       (not (check-collision (get-lowo-at-y lowo (posn-y (new-posn (word-obj-posn wo)))) wo)))
      (make-word-obj (word-obj-word wo) (new-posn (word-obj-posn wo)) true)
      (make-word-obj (word-obj-word wo) (word-obj-posn wo) false)))

;; (list of WordObject) (int)y -> (listof WordObject)
(define (get-lowo-at-y lowo y)
  (if (empty? lowo)
      lowo
      (if (and
           (equal? y (get-y (first lowo)))
           (not (word-obj-is-active (first lowo))))
          (cons (first lowo) (get-lowo-at-y (rest lowo) y))
          (get-lowo-at-y (rest lowo) y))))
;; (list of WordObject) (WordObject) -> Boolean
(define (check-collision lowo wo)
  (ormap (lambda (mem)
            (or
             (and (>= (get-x wo) (get-x mem))
                  (<= (get-x wo) (+ (get-x mem) (image-width (render-word-block-active mem)))))
             (and (>= (get-x mem) (get-x wo))
                  (<= (get-x mem) (+ (get-x wo) (image-width (render-word-block-active wo)))))))
          lowo))

;; make every element of the list go down
;; (list of WordObject) -> (list of WordObject)
(define (go-down lowo)
  (map (lambda (wo)
         (if (word-obj-is-active wo)
             (update-word-obj wo lowo)
             wo))
       lowo))
;; (listof WordObject) -> (listof String)
(define (generate-names lowo)
  (map (lambda (wo)
         (word-obj-word wo))
       lowo))

; Image
(define (rect-block wo)
  (rectangle (* (string-length (word-obj-word wo)) CELL-WIDTH) CELL-HEIGHT "outline" "white"))
;; WordObject -> Image
(define (render-word-block-active wo)
  (overlay (text (word-obj-word wo) CELL-HEIGHT ACTIVE-COLOR)
           (rect-block wo)))
;; WordObject -> Image
(define (render-word-block-stuck wo)
  (overlay (text (word-obj-word wo) CELL-HEIGHT STUCK-COLOR)
           (rect-block wo)))

;; (listof WordObject -> (listof Image)
(define (generate-images lowo)
  (map (lambda (wo)
         (if (word-obj-is-active wo)
             (render-word-block-active wo)
             (render-word-block-stuck wo)
             ))
       lowo))
;; (listof WordObject -> listof Position)
(define (generate-posns lowo)
  (map (lambda (wo)
         (word-obj-posn wo))
       lowo))
;; (listof WordObject -> Image)
;; render board
(define (render-board lowo)
  (place-images
   (generate-images lowo)
   (generate-posns lowo)
   SCENE))


(define (main world)
  (big-bang world
            (name "typaholic")
            (on-tick handle-tick 0.5)
            (to-draw draw-scene)
            (on-key handle-key)
            (stop-when is-game-over)
            ))


;; World -> World
(define (handle-tick w)
  (if (> (random 100) 50)
  (make-world (cons (generate-new-word-obj 0) (go-down (world-lowo w))) (world-input w))
  (make-world (go-down (world-lowo w)) (world-input w))))


(define (draw-scene w) (above (render-board (world-lowo w))
                              (text (world-input w) 24 TYPING-COLOR)))

;; String -> String
(define (delete-last s)
  (if (equal? 0 (string-length s))
      s
      (substring s 0 (- (string-length s) 1))))

;; world key -> world
(define (handle-key w key) (cond
                             [(key=? key "a") (make-world (world-lowo w) (string-append (world-input w) "a"))]
                             [(key=? key "b") (make-world (world-lowo w) (string-append (world-input w) "b"))]
                             [(key=? key "c") (make-world (world-lowo w) (string-append (world-input w) "c"))]
                             [(key=? key "d") (make-world (world-lowo w) (string-append (world-input w) "d"))]
                             [(key=? key "e") (make-world (world-lowo w) (string-append (world-input w) "e"))]
                             [(key=? key "f") (make-world (world-lowo w) (string-append (world-input w) "f"))]
                             [(key=? key "g") (make-world (world-lowo w) (string-append (world-input w) "g"))]
                             [(key=? key "h") (make-world (world-lowo w) (string-append (world-input w) "h"))]
                             [(key=? key "i") (make-world (world-lowo w) (string-append (world-input w) "i"))]
                             [(key=? key "j") (make-world (world-lowo w) (string-append (world-input w) "j"))]
                             [(key=? key "k") (make-world (world-lowo w) (string-append (world-input w) "k"))]
                             [(key=? key "l") (make-world (world-lowo w) (string-append (world-input w) "l"))]
                             [(key=? key "m") (make-world (world-lowo w) (string-append (world-input w) "m"))]
                             [(key=? key "n") (make-world (world-lowo w) (string-append (world-input w) "n"))]
                             [(key=? key "o") (make-world (world-lowo w) (string-append (world-input w) "o"))]
                             [(key=? key "p") (make-world (world-lowo w) (string-append (world-input w) "p"))]
                             [(key=? key "q") (make-world (world-lowo w) (string-append (world-input w) "q"))]
                             [(key=? key "r") (make-world (world-lowo w) (string-append (world-input w) "r"))]
                             [(key=? key "s") (make-world (world-lowo w) (string-append (world-input w) "s"))]
                             [(key=? key "t") (make-world (world-lowo w) (string-append (world-input w) "t"))]
                             [(key=? key "u") (make-world (world-lowo w) (string-append (world-input w) "u"))]
                             [(key=? key "v") (make-world (world-lowo w) (string-append (world-input w) "v"))]
                             [(key=? key "w") (make-world (world-lowo w) (string-append (world-input w) "w"))]
                             [(key=? key "x") (make-world (world-lowo w) (string-append (world-input w) "x"))]
                             [(key=? key "y") (make-world (world-lowo w) (string-append (world-input w) "y"))]
                             [(key=? key "z") (make-world (world-lowo w) (string-append (world-input w) "z"))]
                             [(key=? key "\r") (make-world (try-remove (world-input w) (world-lowo w)) "")]
                             [(key=? key "\b") (make-world (world-lowo w) (delete-last (world-input w)))]
                             [else w]))
;; String (listof WordObj) -> WordObj
(define (find-wo input lowo)
  (if (empty? lowo)
      null
      (if (equal? input (word-obj-word (first lowo)))
          (first lowo)
          (find-wo input (rest lowo)))))

;; String (listof WordObj) -> (listof WordObj)
(define (try-remove input lowo)
  (if (member input (generate-names (get-active-lowo lowo)))
      (remove (find-wo input (get-active-lowo lowo)) (get-active-lowo lowo))
      lowo))

;; (listof WordObject) -> (listof WordObject)
(define (get-active-lowo lowo)
  (filter (lambda (wo)
            (word-obj-is-active wo))
          lowo))
;; (listof WordObject) -> (listof WordObject)
(define (get-stuck-lowo w)
  (filter (lambda (wo)
            (not (word-obj-is-active wo)))
          (world-lowo w)))

;; (listof WordObject) -> Boolean
(define (is-height-zero lowo)
  (ormap (lambda (wo)
           (equal? 0 (get-y wo)))
         lowo))

;; World -> Boolean 
(define (is-game-over w)
  (is-height-zero (get-stuck-lowo w)))


(main init-world)