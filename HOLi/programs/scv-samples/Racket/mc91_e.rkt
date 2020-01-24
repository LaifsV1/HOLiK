#lang racket
(require soft-contract/fake-contract)

(define (mc91 x)
  (if (> x 100) (- x 10)
      (mc91 (mc91 (+ x 11)))))

(provide/contract
   [mc91 (->i ([n integer?]) (res (n) (and/c integer? (λ (a) (implies (<= n 102) (= a 91))))))])