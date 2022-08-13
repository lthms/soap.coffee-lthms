(cleopatra:configure)

(org-babel-do-load-languages
 'org-babel-load-languages
 '((dot . t)
   (shell . t)
   (ocaml . t)))

(setq org-export-with-toc nil
      org-html-htmlize-output-type nil
      org-export-with-section-numbers nil)

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

(beginning-of-buffer)
(insert-nav)
(insert-title)

(let ((outfile (org-export-output-file-name ".html"))
      (org-html-footnotes-section "<!-- %s --><!-- %s -->"))
  (org-export-to-file 'tufte-html outfile nil nil nil t))
