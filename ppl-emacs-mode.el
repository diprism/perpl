(require 'generic-x)

(define-generic-mode 
  'ppl-mode
  '(("{-" . "-}"))
  '()
  '(("--.*" . 'font-lock-comment-face)
    ("\\b\\([0-9][0-9]*\\(\\.[0-9]+\\)?\\)\\b" 1 'font-lock-builtin-face)
    ("->\\|=\\|&\\|\\*\\|;\\|:\\|\\.\\|,\\|\\\\\\||" . 'font-lock-variable-name-face)
    ("data\\|amb\\|factor\\|fail\\|define\\|extern\\|case\\|of\\|let\\|in\\|if\\|then\\|else" . 'font-lock-keyword-face)
    )
  '("\\.ppl$")
  nil
  "Basic highlighting mode for .ppl files"
)

(provide 'ppl-emacs-mode)
