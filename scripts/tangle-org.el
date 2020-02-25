(require 'org)
(cd (getenv "ROOT"))
(setq org-confirm-babel-evaluate nil)
(setq org-src-preserve-indentation t)
(add-to-list 'org-babel-default-header-args
             '(:mkdirp . "yes"))
(org-babel-do-load-languages
 'org-babel-load-languages
 '((shell . t)))
(org-babel-tangle)
