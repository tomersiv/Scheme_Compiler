(define a 'alpha)
(define b 'beta)

(define l ((lambda (x y)
               (list 
                 (lambda () (set! x y))
                 (lambda () (cons x y)))) a b))

(cond ((not (equal? ((car (cdr l))) '(alpha . beta))) 'wrong!)
	((equal? ((car l)) 'dummy) 'wrong!)
	((not (equal? ((car (cdr l))) '(beta . beta))) 'wrong!)
	(else 'ok))

