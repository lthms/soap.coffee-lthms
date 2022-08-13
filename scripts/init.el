;;; cleopatra.el --- The cleopatra Emacs Library
;;; Commentary:
;;; Code:
(require 'package)

(defun cleopatra:ensure-package-installed (&rest packages)
  "Ensure every PACKAGES is installed."
  (mapcar
   (lambda (package)
     (if (package-installed-p package)
         nil
       (package-install package))
     package)
   packages))

(defvar cleopatra:*emacs-dir* (concat (getenv "ROOT") "/.emacs.d/"))

(setq user-emacs-directory cleopatra:*emacs-dir*)
(setq package-user-dir (concat cleopatra:*emacs-dir* "packages"))

(setq package-archives
      '(("gnu"   . "https://elpa.gnu.org/packages/")
        ("melpa" . "https://melpa.org/packages/")))

(package-initialize)

(or (file-exists-p package-user-dir)
    (package-refresh-contents))

(cleopatra:ensure-package-installed 'use-package)

(require 'use-package)

;; -----------------------------------------------------------------------------

(use-package htmlize :ensure t)
(use-package ox-tufte :ensure t)
(use-package tuareg :ensure t
  :config
  (require 'ob-ocaml))

;; -----------------------------------------------------------------------------

(org-babel-do-load-languages
 'org-babel-load-languages
 '((dot . t)
   (shell . t)
   (ocaml . t)))

(setq backup-inhibited t
      org-export-with-toc nil
      org-html-htmlize-output-type nil
      org-export-with-section-numbers nil
      org-html-doctype "html5"
      org-html-html5-fancy t
      org-src-fontify-natively t
      org-export-with-sub-superscripts nil
      org-confirm-babel-evaluate nil
      org-publish-timestamp-directory (concat cleopatra:*emacs-dir* "cache/")
      org-confirm-babel-evaluate nil
      org-src-preserve-indentation t)

(add-to-list 'org-babel-default-header-args
             '(:mkdirp . "yes")
(add-to-list 'org-babel-default-header-args
             '(:noweb-sep . "\n\n")))

(add-to-list 'org-entities-user
             '("im" "\\(" nil "<span class=\"imath\">" "" "" ""))
(add-to-list 'org-entities-user
             '("mi" "\\)" nil "</span>" "" "" ""))

(defun with-keyword (keyword k)
  "Look-up for keyword KEYWORD, and call continuation K with its value."
  (pcase (org-collect-keywords `(,keyword))
    (`((,keyword . ,kw))
     (when kw (funcall k (string-join kw " "))))))

(defun get-keyword (keyword)
  "Look-up for keyword KEYWORD, and returns its value"
  (with-keyword keyword (lambda (x) x)))

(defun get-org-title (path)
  "Fetch the title of an Org file whose path is PATH."
  (with-temp-buffer
    (find-file-read-only path)
    (get-keyword "TITLE")))

(defun insert-title ()
  "Insert the title of the article."
  (with-keyword
   "TITLE"
   (lambda (title)
     (insert
      (format "\n\n@@html:<h1>@@ %s @@html:</h1>@@\n\n" title)))))

(defun insert-series ()
  "Insert the series root link."
  (with-keyword
   "SERIES"
   (lambda (series)
     (insert "\n\n#+attr_html: :class series\n")
     (insert series))))

(defun insert-series-prev ()
  "Insert the series previous article link."
  (with-keyword
   "SERIES_PREV"
   (lambda (series-prev)
     (insert "\n\n#+attr_html: :class series-prev\n")
     (insert series-prev))))

(defun insert-series-next ()
  "Insert the series next article link."
  (with-keyword
   "SERIES_NEXT"
   (lambda (series-next)
     (insert "\n\n#+attr_html: :class series-next\n")
     (insert series-next))))

(defun insert-nav ()
  "Insert the navigation links."
  (when (get-keyword "SERIES")
    (insert "\n\n#+begin_nav\n")
    (insert-series)
    (insert-series-prev)
    (insert-series-next)
    (insert "\n\n#+end_nav\n")))

(defun cleopatra:export-org (input)
  (with-temp-buffer
    (insert-file-contents input)
    (cd (file-name-directory input))
    (beginning-of-buffer)
    (insert-nav)
    (insert-title)

    (let ((outfile (concat (file-name-base input) ".html"))
          (org-html-footnotes-section "<!-- %s --><!-- %s -->"))
      (org-export-to-file 'tufte-html outfile nil nil nil t))))

;; -----------------------------------------------------------------------------

(defun cleopatra:tangle-publish (conf filename _pub-dir)
  (let ((pub-dir (plist-get conf :publishing-directory)))
    (if pub-dir
        (with-temp-buffer
          (find-file-read-only filename)
          (cd (getenv "ROOT"))
          (unless (file-exists-p pub-dir)
            (make-directory pub-dir))
          (cd pub-dir)
          (org-babel-tangle))
      (error "cleopatra: missing :publishing-directory option"))))


(defun cleopatra:export-lp ()
  (setq-local org-publish-project-alist
              '(("lp"
                 :base-directory "site/posts"
                 :publishing-directory "lp"
                 ;; hand-pick which files to tangle (this save a lots of time)
                 :exclude ".*"
                 :include ("CoqffiEcho.org")
                 :publishing-function cleopatra:tangle-publish)))

  (org-publish-all))

(provide 'cleopatra)
;;; cleopatra.el ends here
