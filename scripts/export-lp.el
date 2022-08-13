;; opinionated configuration provided by cleopatra
(cleopatra:configure)

;; allow the execution of shell block code
(org-babel-do-load-languages
 'org-babel-load-languages
 '((shell . t)))

(setq org-publish-project-alist
      '(("lp"
         :base-directory "site/posts"
         :publishing-directory "lp"
         ;; hand-pick which files to tangle (this save a lots of time)
         :exclude ".*"
         :include ("CoqffiEcho.org")
         :publishing-function cleopatra:tangle-publish)))

(org-publish-all)
