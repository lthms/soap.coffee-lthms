(require 'org)
(cd (getenv "ROOT"))
(setq org-confirm-babel-evaluate nil)
(setq org-src-preserve-indentation t)
(org-babel-do-load-languages
 'org-babel-load-languages
 '((shell . t)))
(org-babel-tangle)
