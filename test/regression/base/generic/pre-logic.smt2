; set-option test suite
(set-option :print-success true)
(set-option :my-option quux)
(set-option :my-option-2 "Longer story")
(set-option :verbosity 3)
(set-option :diagnostic-output-channel "/dev/null")
(set-option :foo-option)
(set-option :bar-option 0)
(set-option :pi 3.1415926535879323)
(set-option :hex #xdeafbeef)
(set-option :bin #b1010101)
(set-option :sexprs ( foo "string" #b1010 #xfeb 1.23 2 ( () bar ( :keyword ) ) ))

; get-option test suite
(get-option :print-success)
(get-option :my-option)
(get-option :my-option-2)
(get-option :verbosity)
(get-option :diagnostic-output-channel)
(get-option :foo-option)
(get-option :bar-option)
(get-option :pi)
(get-option :hex)
(get-option :bin)
(get-option :sexprs)

(get-option :non-existing-option)

; set-info test suite
(set-info :foo)
(set-info :interactive-mode true)
(set-info :error-behavior commit-adultery)
(set-info :name "OpenSMT")
(set-info :authors "Muumi-peikko")

; get-info test suite

(get-info :foo)
(get-info :error-behavior)
(get-info :name)
(get-info :authors)

(exit)
(set-logic foo)
