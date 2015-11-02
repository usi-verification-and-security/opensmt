(set-option :print-success true)
(set-option :foo bar)
(get-option :foo)
(get-option :print-success)
; should fail
(set-option :print-success quux)
