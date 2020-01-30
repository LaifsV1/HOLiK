#lang racket
(require soft-contract/fake-contract)

(define (ack m n)
  (cond
    [(= m 0) (+ n 1)]
    [(= n 0) (ack (- m 1) 1)]
    [else (ack (- m 1) (ack m (- n 1)))]))

(provide/contract [ack (integer? integer? . -> . integer?)])

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

(provide/contract
 [dao ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))])

(define (daoe send m)
  (define balance 100)
  (define withdraw
    (λ (m) (if (<= m balance)
              (begin (send m)
                     (set! balance (- balance m))
                     balance)
              balance)))
  (withdraw m)
  balance)

(provide/contract
 [daoe ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))])

(define (f g)
  (define n 0)
  (define inc! (λ () (set! n (+ 1 n))))
  (g inc!)
  n)

(provide/contract
 [f (((-> void?) . -> . void?) . -> . (and/c integer? (>=/c 0)))])

(define (fe g)
  (define n 0)
  (define inc! (λ () (set! n (+ 1 n))))
  (g inc!)
  n)

(provide/contract
 [fe (((-> void?) . -> . void?) . -> . (and/c integer? (>/c 0)))])

(define (factorial z)
  (if (<= z 1)
      1
      (* z (factorial (- z 1)))))

(provide/contract
 [factorial ((and/c integer? (>=/c 0)) . -> . (and/c integer? (>=/c 1)))])

(define (mc91 x)
  (if (> x 100) (- x 10)
      (mc91 (mc91 (+ x 11)))))

(provide/contract
   [mc91 (->i ([n integer?]) (res (n) (and/c integer? (λ (a) (implies (<= n 101) (= a 91))))))])

(define (mc91e x)
  (if (> x 100) (- x 10)
      (mc91 (mc91 (+ x 11)))))

(provide/contract
   [mc91e (->i ([n integer?]) (res (n) (and/c integer? (λ (a) (implies (<= n 102) (= a 91))))))])

(define (mult n m)
  (if (or (<= n 0) (<= m 0)) 0
      (+ n (mult n (- m 1)))))

(define (sqr n) (mult n n))

(provide/contract [mult (integer? integer? . -> . (and/c integer? (>=/c 0)))]
		  [sqr (->i ([n integer?]) (res (n) (and/c integer? (>=/c n))))])

(define (multe n m)
  (if (or (<= n 0) (<= m 0)) 0
      (+ n (multe n (- m 1)))))

(define (sqre n) (multe n n))

(provide/contract [multe (integer? integer? . -> . (and/c integer? (>=/c 0)))]
		  [sqre (->i ([n integer?]) (res (n) (and/c integer? (>=/c (+ n 1)))))])

(define (succ n) (add1 n))

(provide/contract
 [succ (->i ([n (and/c integer? (>=/c 0))])
            (res (n) (and/c integer? (>/c n))))])

(define (succe n) n)

(provide/contract
 [succe (->i ([n (and/c integer? (>=/c 0))])
            (res (n) (and/c integer? (>/c n))))])
