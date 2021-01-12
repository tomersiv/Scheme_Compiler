(letrec ((func (lambda (n) (if n (func #f) 'moshe)))) (func #t))
