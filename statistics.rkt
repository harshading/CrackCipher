#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/string
         (prefix-in utils: "utils.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                 ;;
;; Ciphertext Statistics                                                           ;;
;; =====================                                                           ;;
;;                                                                                 ;;
;; The module should provide a bunch of functions that do statistical analysis of  ;;
;; ciphertext. The output is almost always just an ordered list (counts are        ;;
;; omitted).                                                                       ;;
;;                                                                                 ;;
;; Fill in the body for the skeletons and do not change the arguments. You can     ;;
;; define as many functions as you require, there's no special credit for          ;;
;; implementing/using all of them.                                                 ;;
;;                                                                                 ;;
;; CAUTION:                                                                        ;;
;; 1. Be mindful that bi, tri and quadgrams do not cross word boundaries. Hence,   ;;
;; you must process each word separately.                                          ;;
;;                                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Analyses
(provide cipher-monograms
         cipher-bigrams
         cipher-unique-neighbourhood
         cipher-neighbourhood
         cipher-trigrams
         cipher-quadgrams
         cipher-common-words-single
         cipher-common-words-double
         cipher-common-words-triple
         cipher-common-words-quadruple
         cipher-common-initial-letters
         cipher-common-final-letters
         cipher-common-double-letters
         ;; any other functions of your design come below:

         ;; my-fundoo-analysis
         )

;; Takes ciphertext and produces a list of cipher chars sorted in decreasing
;; order of frequency.
(define (cipher-monograms ciphertext)
  (define (fit p l acc)
    (cond [(null? l) (append acc (list p))]
          [(< (cdar l) (cdr p)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]))
  (define (find-and-fit e l acc)
    (cond [(equal? e (caar l)) (append (fit (cons (caar l) (+ 1 (cdar l))) acc '()) (cdr l))]
          [else (find-and-fit e (cdr l) (append acc (list (car l))))]))
  (define (exists? e l)
    (cond [(null? l) #f]
          [else (if (equal? e (caar l)) #t (exists? e (cdr l)))]))
  (define (amend e l)
    (cond [(null? l) (list (cons e 1))]
          [(exists? e l) (find-and-fit e l '())]
          [else (append l (list (cons e 1)))]))
  (define (cm-with-freq lst acc)
    ;;(displayln acc)
    (cond [(null? lst) acc]
          [(char-alphabetic? (car lst)) (cm-with-freq (cdr lst) (amend (car lst) acc))]
          [else (cm-with-freq (cdr lst) acc)]))
  (map car (cm-with-freq (string->list ciphertext) '())))

;; Takes the cipher-word-list and produces a list of 2-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-bigrams cipher-word-list)
  (define (fit p l acc)
    [cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]])
  (define (find-and-fit bg l acc1)
    (cond [(null? l) (append acc1 (list (cons bg 1)))]
          [(equal? bg (caar l)) (append (fit (cons bg (+ 1 (cdar l))) acc1 '()) (cdr l))]
          [else (find-and-fit bg (cdr l) (append acc1 (list (car l))))]))
  (define (fit-all-of-word word-list l)
    (cond [(null? (cdr word-list)) l]
          [else (fit-all-of-word (cdr word-list) (find-and-fit (list->string (list (car word-list) (cadr word-list))) l '()))]))
  (define (cb-with-freq lst acc)
    ;;(display acc)
    (cond [(null? lst) acc]
          [else (cb-with-freq (cdr lst) (fit-all-of-word (string->list (car lst)) acc))]))
  (map car (cb-with-freq cipher-word-list '())))

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter. Only unique
;; neighbours are to be counted.
;; Consider the character #\o.
;;
;; Takes an argument `mode`:
;; 1. (cipher-unique-neighbourhood cipher-bigrams 'predecessor)
;;    - Count only those unique occurrences where the (given) char preceeds
;;      other char.
;;    - Patterns of the form: "o?"
;; 2. (cipher-unique-neighbourhood cipher-bigrams 'successor)
;;    - Count only those unique occurrences where the (given) char succeeds
;;      other char.
;;    - Patterns of the form: "?o"
;; 3. (cipher-unique-neighbourhood cipher-bigrams 'both)
;;    - Count all unique occurrences where the (given) char neighbours the other
;;      char.
;;    - Patterns of the form "?o" and "o?". Note that this is not sum of (1) and
;;    (2) always.
;;
;; The output is a list of pairs of cipher char and the count of it's
;; neighbours. The list must be in decreasing order of the neighbourhood count.
(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
  (define k0 (remove-duplicates cipher-bigrams-list)) 
  (define org-key (map cons (string->list (build-string 26 (lambda (i) (integer->char (+ i 97))))) (build-list 26 (lambda (x) 0))))
  (define (update k char acc)
    (cond [(equal? char (caar k)) (append acc (list (cons char (+ 1 (cdar k)))) (cdr k))]
           [else (update (cdr k) char (append acc (list (car k))))]))
  (define (helper1 l k)
    (cond [(null? l) k]
          [else (helper1 (cdr l) (update k (last (string->list (car l))) '()))]))
  (define (helper2 l k)
    (cond [(null? l) k]
          [else (helper2 (cdr l) (update k (car (string->list (car l))) '()))]))
  (define (helper3 l k)
    (cond [(null? l) k]
          [(equal? (string-ref (car l) 0) (string-ref (car l) 1)) (helper3 (cdr l) (update k (car (string->list (car l))) '()))]
          [else (helper3 (cdr l) (update (update k (car (string->list (car l))) '()) (last (string->list (car l))) '()))]))
  (define (boo a b) (> (cdr a) (cdr b)))
  (sort (cond [(equal? mode 'successor) (helper1 k0 org-key)]
        [(equal? mode 'predecessor) (helper2 k0 org-key)]
        [else (helper3 k0 org-key)]) boo))
  
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter, but counts each
;; occurrence distinctly. This comment contains 6 bigrams with "w", all with "i" or "h".
;; So "w" has:
;; when mode is 'both,        6 neighbours
;; when mode is 'predecessor, 6 neighbours
;; when mode is 'successor,   0 neighbours
(define (cipher-neighbourhood cipher-word-list mode)
  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  (define (of-word l acc)
    (cond [(null? (cdr l)) acc]
          [else (of-word (cdr l) (append acc (list (list->string (list (car l) (cadr l))))))]))
    
  (define (to-bigrams l acc)
    (cond [(null? l) acc]
          [else (to-bigrams (cdr l) (append acc (of-word (string->list (car l)) '())))]))

    
  (define (helper l)
    (define org-key (map cons (string->list (build-string 26 (lambda (i) (integer->char (+ i 97))))) (build-list 26 (lambda (x) 0))))
  (define (update k char acc)
    (cond [(equal? char (caar k)) (append acc (list (cons char (+ 1 (cdar k)))) (cdr k))]
           [else (update (cdr k) char (append acc (list (car k))))]))
  (define (helper1 l k)
    (cond [(null? l) k]
          [else (helper1 (cdr l) (update k (last (string->list (car l))) '()))]))
  (define (helper2 l k)
    (cond [(null? l) k]
          [else (helper2 (cdr l) (update k (car (string->list (car l))) '()))]))
  (define (helper3 l k)
    (cond [(null? l) k]
          [(equal? (string-ref (car l) 0) (string-ref (car l) 1)) (helper3 (cdr l) (update k (car (string->list (car l))) '()))]
          [else (helper3 (cdr l) (update (update k (car (string->list (car l))) '()) (last (string->list (car l))) '()))]))
  (define (boo a b) (> (cdr a) (cdr b)))
  (sort (cond [(equal? mode 'successor) (helper1 l org-key)]
        [(equal? mode 'predecessor) (helper2 l org-key)]
        [else (helper3 l org-key)]) boo))
  
  (define bigrams (to-bigrams cipher-word-list '()))
  (helper bigrams))

;;;;;;;;;;;;;;;;


;; Takes the cipher-word-list and produces a list of 3-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-trigrams cipher-word-list)
  (define (fit p l acc)
    [cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]])
  (define (find-and-fit bg l acc1)
    (cond [(null? l) (append acc1 (list (cons bg 1)))]
          [(equal? bg (caar l)) (append (fit (cons bg (+ 1 (cdar l))) acc1 '()) (cdr l))]
          [else (find-and-fit bg (cdr l) (append acc1 (list (car l))))]))
  (define (fit-all-of-word word-list l)
    (cond [(null? (cdr word-list)) l]
          [(null? (cddr word-list)) l]
          [else (fit-all-of-word (cdr word-list) (find-and-fit (list->string (list (car word-list) (cadr word-list) (caddr word-list))) l '()))]))
  (define (cb-with-freq lst acc)
    ;;(display acc)
    (cond [(null? lst) acc]
          [else (cb-with-freq (cdr lst) (fit-all-of-word (string->list (car lst)) acc))]))
  (map car (cb-with-freq cipher-word-list '())))

;; Takes the cipher-word-list and produces a list of 4-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-quadgrams cipher-word-list)
  (define (fit p l acc)
    [cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]])
  (define (find-and-fit bg l acc1)
    (cond [(null? l) (append acc1 (list (cons bg 1)))]
          [(equal? bg (caar l)) (append (fit (cons bg (+ 1 (cdar l))) acc1 '()) (cdr l))]
          [else (find-and-fit bg (cdr l) (append acc1 (list (car l))))]))
  (define (fit-all-of-word word-list l)
    (cond [(null? (cdr word-list)) l]
          [(null? (cddr word-list)) l]
          [(null? (cdddr word-list)) l]
          [else (fit-all-of-word (cdr word-list) (find-and-fit (list->string (list (car word-list) (cadr word-list) (caddr word-list) (cadddr word-list))) l '()))]))
  (define (cb-with-freq lst acc)
    (display acc)
    (cond [(null? lst) acc]
          [else (cb-with-freq (cdr lst) (fit-all-of-word (string->list (car lst)) acc))]))
  (map car (cb-with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of single letter words, sorted
;; in decreasing order of frequency. Each element must be a string!
(define (cipher-common-words-single cipher-word-list)
  (define (fit p l acc)
    (cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]))
  (define (find-and-fit str l acc)
    (cond [(null? l) (append acc (list (cons str 1)))]
          [(equal? str (caar l)) (append (fit (cons str (+ 1 (cdar l))) acc '()) (cdr l))]
          [else (find-and-fit str (cdr l) (append acc (list (car l))))]))
  (define (with-freq l acc)
    ;;(displayln acc)
    (cond [(null? l) acc]
          [(= 1 (length (string->list (car l)))) (with-freq (cdr l) (find-and-fit (car l) acc '()))]
          [else (with-freq (cdr l) acc)]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of double letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-double cipher-word-list)
  (define (fit p l acc)
    (cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]))
  (define (find-and-fit str l acc)
    (cond [(null? l) (append acc (list (cons str 1)))]
          [(equal? str (caar l)) (append (fit (cons str (+ 1 (cdar l))) acc '()) (cdr l))]
          [else (find-and-fit str (cdr l) (append acc (list (car l))))]))
  (define (with-freq l acc)
    ;;s(displayln acc)
    (cond [(null? l) acc]
          [(= 2 (length (string->list (car l)))) (with-freq (cdr l) (find-and-fit (car l) acc '()))]
          [else (with-freq (cdr l) acc)]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of triple letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-triple cipher-word-list)
  (define (fit p l acc)
    (cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]))
  (define (find-and-fit str l acc)
    (cond [(null? l) (append acc (list (cons str 1)))]
          [(equal? str (caar l)) (append (fit (cons str (+ 1 (cdar l))) acc '()) (cdr l))]
          [else (find-and-fit str (cdr l) (append acc (list (car l))))]))
  (define (with-freq l acc)
    ;;s(displayln acc)
    (cond [(null? l) acc]
          [(= 3 (length (string->list (car l)))) (with-freq (cdr l) (find-and-fit (car l) acc '()))]
          [else (with-freq (cdr l) acc)]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of four letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-quadruple cipher-word-list)
  (define (fit p l acc)
    (cond [(null? l) (append acc (list p))]
          [(> (cdr p) (cdar l)) (append acc (list p) l)]
          [else (fit p (cdr l) (append acc (list (car l))))]))
  (define (find-and-fit str l acc)
    (cond [(null? l) (append acc (list (cons str 1)))]
          [(equal? str (caar l)) (append (fit (cons str (+ 1 (cdar l))) acc '()) (cdr l))]
          [else (find-and-fit str (cdr l) (append acc (list (car l))))]))
  (define (with-freq l acc)
    ;;s(displayln acc)
    (cond [(null? l) acc]
          [(= 4 (length (string->list (car l)))) (with-freq (cdr l) (find-and-fit (car l) acc '()))]
          [else (with-freq (cdr l) acc)]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of chars that appear at the
;; start of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-initial-letters cipher-word-list)
  (define (fit p l acc2)
    (cond [(null? l) (append acc2 (list p))]
          [(> (cdr p) (cdar l)) (append acc2 (list p) l)]
          [else (fit p (cdr l) (append acc2 (list (car l))))]))
  (define (find-and-fit e l acc1)
    (cond [(null? l) (append acc1 (list (cons e 1)))]
          [(equal? e (caar l)) (append (fit (cons e (+ 1 (cdar l))) acc1 '()) (cdr l))]
          [else (find-and-fit e (cdr l) (append acc1 (list (car l))))]))
  (define (with-freq l acc)
    ;;(displayln acc)
    (cond [(null? l) acc]
          [else (with-freq (cdr l) (find-and-fit (car (string->list (car l))) acc '()))]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of chars that appear at the
;; end of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-final-letters cipher-word-list)
  (define (fit p l acc2)
    (cond [(null? l) (append acc2 (list p))]
          [(> (cdr p) (cdar l)) (append acc2 (list p) l)]
          [else (fit p (cdr l) (append acc2 (list (car l))))]))
  (define (find-and-fit e l acc1)
    (cond [(null? l) (append acc1 (list (cons e 1)))]
          [(equal? e (caar l)) (append (fit (cons e (+ 1 (cdar l))) acc1 '()) (cdr l))]
          [else (find-and-fit e (cdr l) (append acc1 (list (car l))))]))
  (define (with-freq l acc)
    (displayln acc)
    (cond [(null? l) acc]
          [else (with-freq (cdr l) (find-and-fit (last (string->list (car l))) acc '()))]))
  (map car (with-freq cipher-word-list '())))

;; Takes the cipher word list and produces a list of chars that appear as
;; consecutive double letters in some word, sorted in decreasing order of
;; frequency. Each element must thus be a char!
(define (cipher-common-double-letters cipher-word-list)
  (define (doubles l acc)
    (cond [(null? l) acc]
          [(equal? (string-ref (car l) 0) (string-ref (car l) 1)) (doubles (cdr l) (append acc (list (car l))))]
          [else (doubles (cdr l) acc)]))
  (doubles (cipher-bigrams cipher-word-list) '()))
       
