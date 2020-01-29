#lang racket

(provide/contract [ack (->i ([m (>=/c 0)] [n (>=/c 0)]) (res (m n) (>=/c n)))])

(define (ack m n)
  (cond
    [(= m 0) (+ n 1)]
    [(= n 0) (ack (- m 1) 1)]
    [else (ack (- m 1) (ack m (- n 1)))]))
