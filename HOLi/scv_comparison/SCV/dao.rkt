#lang racket

(provide/contract
 [dao ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))])

(define (dao send m)
  (define balance 100)
  (define withdraw
    (λ (m) (if (<= m balance)
              (begin (set! balance (- balance m))
                     (send m)
                     balance)
              balance)))
  (withdraw m)
  balance)
