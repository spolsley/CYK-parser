#lang racket

;Author Seth Polsley
;Date: 5/8/14
;Description: CYK parser - parses either words (strings) or sentences (lists) on a grammar

(require racket/trace racket/vector)

(define : vector-ref)
(define := vector-set!)

; CYK Parser
(define (cyk input grammar starts)
  (cond
    ((string? input)(cyk-word input grammar starts))
    ((list? input)(cyk-sent input grammar starts))
    (else '(ERROR: Unsupported input format. Use lists or strings))))

(define (cyk-word s g starts)
  (call/cc
   (λ(K)
     (define terminals '())
     (define non-terminals '())
     (define N (string-length s))
     (define M (length g))
     (define rules (make-hash))
     (let ((j 1))
       (dict-for-each g(λ(k v)(hash-set! rules k j)(set! j (+ j 1)))))
     (define P (make-vector (+ N 1)))
     (for ([i (in-range 1 (+ N 1))])
       (:= P i (make-vector (+ N 1)))
       (for ([j (in-range 1 (+ N 1))])
         (:= (: P i) j (make-vector (+ M 1) #f))))
     (for ([i (in-range 1 (+ N 1))])
       (let ((a (substring s (- i 1) i)))
         (dict-for-each g(λ(k v)(when(string=? v a)
                                  (begin(:=(:(: P i)1)(hash-ref rules k) #t)
                                        (set! terminals (cons (list k '-> v) terminals))))))))
     (set! terminals (reverse terminals))
     (when(< (length terminals)N)(K '(ERROR: Input contains character not given in grammar)))
     (for ([length (in-range 2 (+ N 1))])
       (for ([start (in-range 1 (+(- N length)2))])
         (for ([len1 (in-range 1 length)])
           (let ((len2 (- length len1)))
             (dict-for-each g(λ(k v)(when(not(string=? v(string-downcase v)))
                                      (when(and (:(:(: P start)len1)(hash-ref rules(substring v 0 1)))
                                                (:(:(: P (+ start len1))len2)(hash-ref rules(substring v 1 2))))
                                        (begin (:=(:(: P start)length)(hash-ref rules k) #t)
                                               (set! non-terminals (cons (list k '-> v) non-terminals)))))))
          ))))
     (when(< (length non-terminals)(- N 1))(K (cons #f (cons non-terminals terminals))))
     (define result #f)
     (for ([i (vector-length starts)])
       (for ([j (in-range 1 (+ N 1))])
         (when(eq?(:(:(: P 1)j)(hash-ref rules(: starts i)))#t)(set! result #t))))
     (cons result (cons non-terminals terminals)))))

(define (cyk-sent s g starts)
  (call/cc
   (λ(K)
     (define terminals '())
     (define non-terminals '())
     (define sent (list->vector s))
     (define N (vector-length sent))
     (define M (length g))
     (define rules (make-hash))
     (let ((j 1))
       (dict-for-each g(λ(k v)(hash-set! rules k j)(set! j (+ j 1)))))
     (define P (make-vector (+ N 1)))
     (for ([i (in-range 1 (+ N 1))])
       (:= P i (make-vector (+ N 1)))
       (for ([j (in-range 1 (+ N 1))])
         (:= (: P i) j (make-vector (+ M 1) #f))))
     (for ([i (in-range 1 (+ N 1))])
       (let ((a (: sent (- i 1))))
         (dict-for-each g(λ(k v)(when(eq? v a)
                                  (begin(:=(:(: P i)1)(hash-ref rules k) #t)
                                        (set! terminals (cons (list k '-> v) terminals))))))))
     (set! terminals (reverse terminals))
     (when(< (length terminals)N)(K '(ERROR: Input contains word not given in grammar)))
     (for ([length (in-range 2 (+ N 1))])
       (for ([start (in-range 1 (+(- N length)2))])
         (for ([len1 (in-range 1 length)])
           (let ((len2 (- length len1)))
             (dict-for-each g(λ(k v)(when(pair? v)
                                      (when(and (:(:(: P start)len1)(hash-ref rules(car v)))
                                                (:(:(: P (+ start len1))len2)(hash-ref rules(cadr v))))
                                        (begin (:=(:(: P start)length)(hash-ref rules k) #t)
                                               (set! non-terminals (cons (list k '-> v) non-terminals)))))))
          ))))
     (when(< (length non-terminals)(- N 1))(K (cons #f (cons non-terminals terminals))))
     (define result #f)
     (for ([i (vector-length starts)])
       (for ([j (in-range 1 (+ N 1))])
         (when(eq?(:(:(: P 1)j)(hash-ref rules(: starts i)))#t)(set! result #t))))
     (cons result (cons non-terminals terminals)))))

; Examples parsing strings
; The grammar uses a dictionary of string pairs
; Uppercase letters are non-terminals and lowercase letters are terminals
(define g1 '(("S"."AD")
             ("S"."AC")
             ("D"."BE")
             ("E"."CF")
             ("A"."a")("B"."b")("C"."c")("F"."f")))
(define starts1 #("S"))
(cyk "a" g1 starts1)
(cyk "abba" g1 starts1)
(cyk "abcf" g1 starts1)
(cyk "abfc" g1 starts1)
(cyk "aaaa" g1 starts1)
(cyk "bbab" g1 starts1)
(cyk "cfa" g1 starts1)
(cyk "ac" g1 starts1)
(cyk "abcfafaf" g1 starts1)

; Examples parsing sentences
; The grammar uses a dictionary of symbol pairs
; A symbol whose cdr is a pair is non-terminals while symbols leading to symbols are terminals
(define g2 '((S . (N V))
             (V . (V A))
             (N . she)(V . jogs)(A . daily)))
(define starts2 #(S))
(cyk '(she jogs) g2 starts2)
(cyk '(she jogs daily) g2 starts2)

; The CYK parser above is basically a membership test
; It will tell if a given input is in the given grammar
; However, there may be multiple parses of a single sentence that are each valid for the grammar
; We see this in the sentences below
; The CYK parser can correctly determine whether or not the sentences are in the grammar
; However, it does not provide a definitive derivation
; This is because I just added a short list of some of the rules that had been applied, which may include different parsings
; The more advanced solution to this problem is to use probabilities for each rule
; The probability of a given rule could be used by the CYK algorithm rather than simply "True" or "False"
(define g3 '((S . (NP VP))
             (NP . (NP RC))
             (NP . (PN N))
             (RC . (NP V))
             (VP . (V NP))
             (PN . Buffalo)(N . buffalo)(V . buffalo)))
(define starts3 #(S))
; See http://en.wikipedia.org/wiki/Buffalo_buffalo_Buffalo_buffalo_buffalo_buffalo_Buffalo_buffalo
; for more details about this example
(cyk '(Buffalo buffalo Buffalo buffalo buffalo buffalo Buffalo buffalo) g3 starts3)

(define g4 '((S . (NP VP))
             (S . (NP V))
             (NP . (Art N))
             (NP . (AP N))
             (AP . (Art Adj))
             (VP . (V Adv))
             (Art . the)(Adj . girl)(N . guides)(V . guides)(V . fish)(Adv . fish)))
(define starts4 #(S))
(cyk '(the girl guides fish) g4 starts4)

; With a probabilities-driven parser, we could do a lot more to deal with ambiguous sentences
; However, there are a lot of sentences that are not ambiguous, and this simple parser can still do a lot on those
(define (subject sent)
  (let ((parsed (cyk sent DICTIONARY #(S))))
    (if(eq? (car parsed) #t)
       (caddr (assoc 'N (cddr parsed)))
       '(ERROR: The sentence is not valid))))

(define (action sent)
  (let ((parsed (cyk sent DICTIONARY #(S))))
    (if(eq? (car parsed) #t)
       (caddr (assoc 'V (cddr parsed)))
       '(ERROR: The sentence is not valid))))

(define DICTIONARY
  '((S . (NP VP))
    (NP . (NP RC))
    (NP . (PN N))
    (NP . (AP N))
    (AP . (Art AP))
    (AP . (Art Adj))
    (AP . (Adj Adj))
    (RC . (NP V))
    (VP . (V NP))
    (VP . (V Adv))
    
    (Art . the)(Art . an)(Art . a)
    (Adj . fast)(Adj . strong)
    (PN . Seth)
    (N . man)(N . woman)
    (V . runs)(V . jogs)
    (Adv . daily)(Adv . frequently)(Adv . often)))

(subject '(the strong man jogs often))
(action '(a fast woman runs frequently))

; Here we see that some basic information can be extracted from non-ambiguous sentences using this parser