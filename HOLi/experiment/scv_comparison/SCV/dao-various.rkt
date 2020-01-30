#lang racket

(provide/contract
 [dao1 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao2-e ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao3 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao4-e ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao5 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao6-e ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao7 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao8-e ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao9 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao10-e ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))])

(define (dao1 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (set! n (- n m))
                     (send m)
                     n)
              n)))
  (withdraw m)
  n)

(define (dao2-e send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao3 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (set! n (- n m))
                     (send m)
                     n)
              n)))
  (withdraw m)
  n)

(define (dao4-e send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao5 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (set! n (- n m))
                     (send m)
                     n)
              n)))
  (withdraw m)
  n)

(define (dao6-e send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao7 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (set! n (- n m))
                     (send m)
                     n)
              n)))
  (withdraw m)
  n)

(define (dao8-e send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao9 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (set! n (- n m))
                     (send m)
                     n)
              n)))
  (withdraw m)
  n)

(define (dao10-e send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)