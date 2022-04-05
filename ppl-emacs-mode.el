(require 'generic-x)

;(defface ppl-keyword-face
;   '((((background light))
;      (:foreground "#8ac6f2" :weight bold))
;     (((background dark))
;      (:foreground "#8ac6f2" :weight bold)))
;   "Face for keywords"
;   :group 'ppl-highlight-faces)
;
;(defface ppl-dist-face
;   '((((background light))
;      (:foreground "darkgrey" :slant italic))
;     (((background dark))
;      (:foreground "lightgrey" :slant italic)))
;   "Face for fail, amb, and uniform"
;   :group 'ppl-highlight-faces)
;
;(defface ppl-punct-face
;   '((((background light))
;      (:foreground "dark slate blue"))
;     (((background dark))
;      (:foreground "plum")))
;   "Face for punctuation"
;   :group 'ppl-highlight-faces)
;
;(defface ppl-var-face
;   '((((background light))
;      (:foreground "#cae682"))
;     (((background dark))
;      (:foreground "#cae682")))
;   "Face for variables"
;   :group 'ppl-highlight-faces)

(define-generic-mode 
  'ppl-mode
  '(("{-" . "-}"))
  '()
  '(("--.*" . 'font-lock-comment-face)
    ("=\\|&\\|\\*\\|->\\|;\\|:\\|\\.\\|,\\|\\\\\\||" . 'font-lock-builtin-face);'ppl-punct-face)
    ("\\(^\\|[^A-Za-z0-9\\'_]\\)\\(define\\|extern\\|data\\|case\\|of\\|let\\|in\\|sample\\|if\\|then\\|else\\)\\(^\\|[^A-Za-z0-9\\'_]\\)" 2 'font-lock-keyword-face);'ppl-keyword-face)
    ("\\b\\(amb\\|fail\\|uniform\\)\\b" 1 'font-lock-string-face);'ppl-dist-face)
    ("\\b\\([A-Za-z0-9\\'_]+\\)\\b" 1 'font-lock-function-name-face);'ppl-var-face)
    )
  '("\\.ppl$")
  nil
  "Basic highlighting mode for .ppl files"
)

(provide 'ppl-emacs-mode)
