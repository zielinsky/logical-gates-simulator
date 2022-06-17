#lang racket
(require rackunit)
(require data/heap)

(provide sim? wire?
         (contract-out
          [make-sim        (-> sim?)]
          [sim-wait!       (-> sim? positive? void?)]
          [sim-time        (-> sim? real?)]
          [sim-add-action! (-> sim? positive? (-> any/c) void?)]

          [make-wire       (-> sim? wire?)]
          [wire-on-change! (-> wire? (-> any/c) void?)]
          [wire-value      (-> wire? boolean?)]
          [wire-set!       (-> wire? boolean? void?)]

          [bus-value (-> (listof wire?) natural?)]
          [bus-set!  (-> (listof wire?) natural? void?)]

          [gate-not  (-> wire? wire? void?)]
          [gate-and  (-> wire? wire? wire? void?)]
          [gate-nand (-> wire? wire? wire? void?)]
          [gate-or   (-> wire? wire? wire? void?)]
          [gate-nor  (-> wire? wire? wire? void?)]
          [gate-xor  (-> wire? wire? wire? void?)]

          [wire-not  (-> wire? wire?)]
          [wire-and  (-> wire? wire? wire?)]
          [wire-nand (-> wire? wire? wire?)]
          [wire-or   (-> wire? wire? wire?)]
          [wire-nor  (-> wire? wire? wire?)]
          [wire-xor  (-> wire? wire? wire?)]

          [flip-flop (-> wire? wire? wire? void?)]))


(struct sim ([time #:mutable] [heap #:mutable]))
(struct wire ([value #:mutable] [sim #:mutable] [actions #:mutable]))
(struct event (time function))


(define (make-sim)
  (sim 0 (make-heap
          (lambda (x y) (<= (event-time x) (event-time y))))))

(define (sim-wait! s t)
  (define end-time (+ (sim-time s) t))
  (define (sim-skip s)
    (if (or (= (heap-count (sim-heap s)) 0) 
            (< end-time (event-time (heap-min (sim-heap s)))))
        (set-sim-time! s end-time)
        (begin
          (let ([f (event-function (heap-min (sim-heap s)))])
            (set-sim-time! s (event-time (heap-min (sim-heap s))))
            (heap-remove-min! (sim-heap s))
            (f)
            (sim-skip s)))))
  (set-sim-time! s (+ (sim-time s) t))
  (sim-skip s))

(define (sim-add-action! s t f)
  (heap-add! (sim-heap s) (event (+ (sim-time s) t) f)))


(define (make-wire s)
  (wire #f s '()))

(define (call-actions xs)
  (if (null? xs)
      (void)
      (begin
        ((car xs))
        (call-actions (cdr xs)))))

(define (wire-set! w v)
  (if (eq? (wire-value w) v)
      (void)
      (begin
        (set-wire-value! w v)
        (call-actions (reverse (wire-actions w))))))

(define (wire-on-change! w f)
  (set-wire-actions! w (cons f (wire-actions w)))
  (f))


(define (bus-set! wires value)
  (match wires
    ['() (void)]
    [(cons w wires)
     (begin
       (wire-set! w (= (modulo value 2) 1))
       (bus-set! wires (quotient value 2)))]))

(define (bus-value ws)
  (foldr (lambda (w value) (+ (if (wire-value w) 1 0) (* 2 value)))
         0
         ws))

(define (gate-not a b)
  (define (not-action)
    (wire-set! a (not (wire-value b))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 1 not-action))))

(define (gate-and a b c)
  (define (and-action)
    (wire-set! a (and (wire-value b) (wire-value c))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 1 and-action)))
  (wire-on-change! c (lambda () (sim-add-action! (wire-sim c) 1 and-action))))

(define (gate-nand a b c)
  (define (nand-action)
    (wire-set! a (not (and (wire-value b) (wire-value c)))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 1 nand-action)))
  (wire-on-change! c (lambda () (sim-add-action! (wire-sim c) 1 nand-action))))

(define (gate-or a b c)
  (define (or-action)
    (wire-set! a (or (wire-value b) (wire-value c))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 1 or-action)))
  (wire-on-change! c (lambda () (sim-add-action! (wire-sim c) 1 or-action))))

(define (gate-nor a b c)
  (define (nor-action)
    (wire-set! a (not (or (wire-value b) (wire-value c)))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 1 nor-action)))
  (wire-on-change! c (lambda () (sim-add-action! (wire-sim c) 1 nor-action))))

(define (gate-xor a b c)
  (define (xor-action)
    (wire-set! a (xor (wire-value b) (wire-value c))))
  (wire-on-change! b (lambda () (sim-add-action! (wire-sim b) 2 xor-action)))
  (wire-on-change! c (lambda () (sim-add-action! (wire-sim c) 2 xor-action))))

(define (wire-not b)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-not a b)
    a))

(define (wire-and b c)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-and a b c)
    a))

(define (wire-nand b c)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-nand a b c)
    a))

(define (wire-or b c)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-or a b c)
    a))

(define (wire-nor b c)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-nor a b c)
    a))

(define (wire-xor b c)
  (define a (make-wire (wire-sim b)))
  (begin
    (gate-xor a b c)
    a))



(define (flip-flop out clk data)
  (define sim (wire-sim data))
  (define w1  (make-wire sim))
  (define w2  (make-wire sim))
  (define w3  (wire-nand (wire-and w1 clk) w2))
  (gate-nand w1 clk (wire-nand w2 w1))
  (gate-nand w2 w3 data)
  (gate-nand out w1 (wire-nand out w3)))


