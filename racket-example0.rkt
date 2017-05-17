;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-beginner-reader.ss" "lang")((modname racket-example0) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(require 2htdp/image)

;; draw the background of the image
(define WIDTH 80)
(define HEIGHT 92)
(define BACKGROUND (rectangle WIDTH HEIGHT "outline" "black"))

;; draw the text part of the sign
(define TEXT_SIZE 20)
(define TEXT_COLOR "black")
(define SPEED (text "SPEED" TEXT_SIZE TEXT_COLOR))
(define LIMIT (text "LIMIT" TEXT_SIZE TEXT_COLOR))
(define TEXT (above SPEED
                    LIMIT))

;; draw the number part of the sign
(define SPEED_SIZE 30)
(define SPEED_COLOR "black")
; Number -> Image
(define (draw-speed speed)
  (text (number->string speed) SPEED_SIZE SPEED_COLOR))

;; draw the unit part of the sign
(define UNIT_SIZE 15)
(define UNIT_COLOR "black")
; String -> Image
(define (draw-unit unit)
  (text unit UNIT_SIZE UNIT_COLOR))

; Number String -> Image
(define (draw-speed-unit speed unit)
  (beside (draw-speed speed) (draw-unit unit)))

;; draw the content of the sign
; Number String -> Image
(define (draw-content speed unit)
  (above TEXT
         (draw-speed-unit speed unit)))

;; draw the sign
; Number String -> Image
(define (draw-all speed limit)
  (overlay (draw-content speed limit)
           BACKGROUND))

(draw-all 15 "mph")