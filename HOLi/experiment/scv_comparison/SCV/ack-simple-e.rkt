#lang racket

(provide/contract [ack (exact-integer? exact-integer? . -> . (and/c exact-integer? (>=/c 0)))])

(define (ack m n)
  (cond
    [(= m 0) (+ n 1)]
    [(= n 0) (ack (- m 1) 1)]
    [else (ack (- m 1) (ack m (- n 1)))]))
