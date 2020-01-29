#lang racket

(provide/contract
 [dao1 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao2 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao3 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao4 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao5 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao6 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao7 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao8 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao9 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))]
 [dao10 ((-> integer? void?) integer? . -> . (and/c integer? (>=/c 0)))])

(define (dao1 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao2 send m)
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
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao4 send m)
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
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao6 send m)
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
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao8 send m)
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
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)

(define (dao10 send m)
  (define n 100)
  (define withdraw
    (λ (m) (if (<= m n)
              (begin (send m)
                     (set! n (- n m))
                     n)
              n)))
  (withdraw m)
  n)