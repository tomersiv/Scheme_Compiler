(define fact (lambda (n)
        (if (zero? n)
        1
        (* n (fact (- n 1))))))


(let ((fact10  (fact 10)))
    `(fact 10 is: ,fact10))