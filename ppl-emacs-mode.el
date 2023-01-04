(require 'generic-x)

(define-generic-mode 
  'ppl-mode
  '(("{-" . "-}"))
  '()
  '(("--.*" . 'font-lock-comment-face)
    ("\\b\\([0-9][0-9]*\\(\\.[0-9]+\\)?\\)\\b" 1 'font-lock-builtin-face)
    ("->\\|=\\|&\\|\\*\\|;\\|:\\|\\.\\|,\\|\\\\\\||" . 'font-lock-variable-name-face)
    ("\\bdata\\b\\|\\bamb\\b\\|\\bfactor\\b\\|\\bfail\\b\\|\\bdefine\\b\\|\\bextern\\b\\|\\bcase\\b\\|\\bof\\b\\|\\blet\\b\\|\\bin\\b\\|\\bif\\b\\|\\bthen\\b\\|\\belse\\b" . 'font-lock-keyword-face)
    )
  '("\\.ppl$")
  nil
  "Basic highlighting mode for .ppl files"
)

(provide 'ppl-emacs-mode)
