;; Requires ocp-indent to be installed with opam
;; Run this file using:
;; emacs -q -batch **/*.ml -l [full path to kiln]/untabify.el
 
(load-file "~/.opam/4.02.1/share/emacs/site-lisp/ocp-indent.el")

 (if (< 1 (count-windows))
     (delete-other-windows (selected-window)))
 (catch 'tag
   (while t
     (untabify (point-min) (point-max))
     (ocp-indent-region (point-min) (point-max))
     (if buffer-file-name  ; nil for *scratch* buffer
         (progn
           (write-file buffer-file-name)
           (kill-buffer (current-buffer)))
       (throw 'tag t))))