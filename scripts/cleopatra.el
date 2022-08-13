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

(defvar cleopatra:*emacs-dir* (concat (getenv "ROOT") "/.cleopatra/emacs.d/"))

(setq user-emacs-directory cleopatra:*emacs-dir*)
(setq package-user-dir (concat cleopatra:*emacs-dir* "packages"))

(setq package-archives
      '(("gnu"   . "https://elpa.gnu.org/packages/")
        ("melpa" . "https://melpa.org/packages/")
        ("org" . "https://orgmode.org/elpa/")))

(package-initialize)

(or (file-exists-p package-user-dir)
    (package-refresh-contents))

(cleopatra:ensure-package-installed 'use-package)

(require 'use-package)

(use-package org :ensure org-plus-contrib :pin org)
(use-package htmlize :ensure t)

(defun cleopatra:configure ()
  (setq backup-inhibited t)
  (setq org-html-doctype "html5")
  (setq org-html-html5-fancy t)
  (setq org-src-fontify-natively t)
  (setq org-export-with-sub-superscripts nil)
  (setq org-confirm-babel-evaluate nil)
  (setq org-publish-timestamp-directory
        (concat cleopatra:*emacs-dir* "cache/"))
  (setq org-confirm-babel-evaluate nil)
  (setq org-src-preserve-indentation t)
  (add-to-list 'org-babel-default-header-args
               '(:mkdirp . "yes"))
  (add-to-list 'org-babel-default-header-args
               '(:noweb-sep . "\n\n")))

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

(provide 'cleopatra)
;;; cleopatra.el ends here
