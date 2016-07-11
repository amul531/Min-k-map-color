;; GMU - CS 580
;; December 2, 2014

(load "states.cl") ;; *50-states*
(load "india.lisp")  ;; *11-states*, *15-states*, *23-states*
(defvar *australia*)
(setf *australia* '((WA  (NT SA))
                    (NT  (WA SA Q))
                    (SA  (WA NT Q NSW V))
                    (Q   (NT SA NSW))
                    (NSW (SA Q V))
                    (V   (SA NSW))
                    (TM  ())))

(load "countriesmap.lisp")
(defvar *colors*)
(setf *colors* '(R G B Y))

;; Debugging print statements
(defvar *debug*)
(setf *debug* 0) ; disable debugging
;(setf *debug* 1) ; level 1 debugging
;(setf *debug* 2) ; level 2 debugging
;(setf *debug* 3) ; level 3 debugging

;; Print a list, but only if *debug* >= level
(defun debug-list (str lst &optional (level 1))
  (let ((fmtstr (format nil "~~~dd ~~a: ~~a~~%" (* 2 level))))
    (if (>= *debug* level)
      (format t fmtstr (length lst) str lst))))

;; Return x in list where val == which(x) (which is built-in 'first' by default)
;; For example, find a country in a coloring list ((A R) (B G) (C Y) ...):
;;           (ffind coloring "Zimbabwe" :which #'first)
;;  Find everything which has color 'G:
;;           (ffind coloring 'G :which #'second)
(defun ffind (val alist &key (which #'first))
  (mapcan #'(lambda (x) 
              (if (equal val (funcall which x))
                (list x)
                nil))
          alist)) 

;; Deep copy of nested lists
(defun copyMap (map)
  (mapcar #'(lambda (x) (if (atom x) x (copyMap x))) map))

;; Cleans out a map's neighbors given a vertex to remove
(defun cleanNeighbors (alist vertex)
  (mapcar #'(lambda (state) 
              (let ((node (first state)) (adj (second state)))
                ; Use new adjacency list with vertex removed
                (list node (remove vertex adj :test #'equal))))
          alist))


;; Remove all nodes with 0 or 1 neighbors.
;; alist - association list e.g. '( (A (B C D)) (B (A D)) ... )
;; returns the map of all the nodes with 0 or 1 neighbors removed
(defun rem01 (alist)
  (let ((newMap nil) (deleted nil))
    (if (null alist) nil
      (dolist (s alist)
        ; if there are 1 or less neighbors put them into the deleted list
        (if (<= (list-length (second s)) 1)
          (setf deleted (append deleted (list (first s))))
          (setf newMap (append newMap (list s)))))) 
    ; if nothing was deleted return newMap
    (if (null deleted) newMap
      (let nil ; else
        ; clean the deleted nodes out of the neighbors and repeat
        (dolist (d deleted)
          (setf newMap (cleanNeighbors newMap d)))
        (setf newMap (rem01 newMap))))
    newMap))


;; Greedy algorithm implementation.
;; alist - association list e.g. '( (A (B C D)) (B (A D)) ... )
;; fullalist - unedited/original alist
;; cutset - list of nodes to be cut out to make the remaining map a tree
(defun GA (alist fullalist &optional (cutset nil))
  ;;repeatedly remove all nodes with 0 or 1 neighbors
  (setf alist (rem01 alist))
  (if (null alist) nil
  ;;find the node with the highest number of neighbors
    (let ((maxdegree 0) (maxnode nil))
      (dolist (n alist)
        (if (>= (list-length (second n)) maxdegree)
          (dolist (f fullalist)
            (cond ((equal (first n) (first f))
                   (setf maxdegree (list-length (second n)))
                   (setf maxnode n))))))
      ;;remove the node with highest degree from the list
      (setf alist (remove maxnode alist))
      ;;clean up the neighbors of the maxnode
      (setf alist (cleanNeighbors alist (first maxnode)))
      (dolist (f fullalist)
        (if (equal (first maxnode) (first f))
          (let ((node (list maxnode)))
            ;;save the original maxnode in a cutset list
            (setf cutset (append cutset node))
            ;;recursively call to obtain a full cutset
            (setf cutset (append node (GA alist fullalist cutset))))))
      cutset)));;returns the list of all the cutset nodes
	  


;; helps separate the trees with recursive calls to this
(defun separateTreeHelper (alist state)
  (if (null alist) nil
    (let ((curr state))
      (let ((node (first curr)) (adj (second curr)))
        ;; removes current node from alist and cleans up all of its neighbors
        (setf alist (remove curr alist))
        (setf alist (cleanNeighbors alist node))
        (dotimes (i (length adj))
          (dolist (x alist)
            (if (equal (nth i adj) (first x))
			;;recursive call for all neighbors
              (setf alist(separateTreeHelper alist x))))))))
  alist)

;; Separates all the trees from the remaining alist.
;; alist - association list e.g. '( (A (B C D)) (B (A D)) ... )
(defun separateTrees (alist)
  (if (null alist) nil
    (let ((rList (list (first alist))))
      ;add the first element to rList 
      (setf alist (separateTreeHelper alist (first alist)))
      ;;appends the root of all trees in the map and returns it
      (setf rList (append rList (separateTrees alist)))
      rList)))

;; Whether a complete coloring is valid for the given the association list
; alist    - association list e.g. '( (A (B C D)) (B (A D)) ... )
; coloring - coloring of nodes e.g. ((A R) (B B) (C G) ...)
(defun valid-coloring (alist coloring)
  ; For each pair
  (dolist (pair coloring)
    (let ((color (second pair))
          (adj (second (assoc (first pair) alist))))
      ; Make sure it doesn't conflict with any adjacency list
      (dolist (place2 adj)
        (if (eq color (second (assoc place2 coloring)))
          ; Break immediately if we find a contradiction
          (return-from valid-coloring nil)))))
  t) ; Return true if everything was okay



;; Handles the coloring for cutset and the trees
(defun colorHelper (map coloring start)
  (let ((curr nil)) 
    ; find the current node in the map to be able to get neighbors
    (dolist (c map)
      (cond
        ((equal start (first c))
         (setf curr c))))
    ; assign the coloring to the current node
    ; and remove the color from neighboring nodes
    (dolist (c coloring)
      (cond 
        ((equal (first c) (first curr))
         (setf (second c) (first (second c)))
         (dolist (c2 coloring)
           (dolist (neigh (second curr))
             (cond
               ((equal (first c2) neigh)
                (setf (second c2) (remove (second c) (second c2))))))))))
    ; loop for recursive calls to neighbors of the current node
    (dolist (neigh (second curr))
      (dolist (c coloring)
        (cond
          ((and (equal (first c) neigh) (not (atom (second c))))
           (setf map (cleanneighbors map neigh))
           (setf coloring (colorHelper map coloring neigh))))))
    ; return the coloring list
    coloring))  

;; Rebuild a tree given a root node and a list of all nodes in the map
(defun rebuildTree (start treelist)
  (let ((rList nil) (temp nil))
    (setf temp (copymap treelist))
    (setf rList (append rList (list start)))
    (setf temp (cleanNeighbors temp (first start)))
    (dolist (neigh (second start))
      (dolist (node temp)
        (cond
          ((equal neigh (first node))
           (setf rList (append rList (rebuildTree node temp)))))))
    rList))

;; Run the complete cutset conditioned coloring algorithm
(defun coloring (alist)
  (let ((cutset nil)       ; cutset map
        (cutset-nodes nil) ; cutset nodes
        (treelist alist)   ; trees map (cutset removed)
        (treelist-nodes nil)   ; trees nodes
        (temp nil) (temp1 nil)
        (cutsetColor nil)
        (treeColor nil)
        (sepTrees nil))

    (debug-list "input map" alist)

    ; compute the cutset with the greedy algorithm
    (setf cutset-nodes (mapcar #'first (GA treelist treelist)))

    (debug-list "cutset nodes" cutset-nodes)

    ; get cutset with all neighbors attached
    (dolist (c cutset-nodes)
      (dolist (s alist)
        (let ((n (first s))     ; tree node
              (adj (second s))) ; adjacent nodes
          (if (equal c n)
            (push (list n (copy-list adj)) cutset)))))

    ; clean cutset nodes out of tree map
    (dolist (c cutset-nodes)
      (setf treelist (remove (assoc c treelist) treelist)))
    (dolist (c cutset-nodes)
      (setf treelist (cleanNeighbors treelist c)))

    (setf treelist-nodes (mapcar #'first treelist))
    (debug-list "treelist nodes" treelist-nodes)

    ; clean tree nodes out of cutset map
    (dolist (tn treelist-nodes)
      (setf cutset (remove (assoc tn cutset) cutset)))
    (dolist (tn treelist-nodes)
      (setf cutset (cleanNeighbors cutset tn)))

    ; give each node a list of its possible colors
    ; e.g. ( (GERMANY (R G B Y)) (FRANCE (R G B Y)) )
    (setf cutsetColor (mapcar #'(lambda (c) (list c *colors*)) cutset-nodes))
    (setf treeColor (mapcar #'(lambda (tn) (list tn *colors*)) treelist-nodes))

    (debug-list "cutset colors" cutsetColor 2)
    (debug-list "cutset map" cutset 2)
    (debug-list "tree colors" treeColor 2)
    (debug-list "treelist map" treelist 2)

    ; do cutset coloring
    ; separate the cutset into connected pieces
    (let ((sepCutsets (separateTrees cutset)))
      (dolist (sepSet sepCutsets)
        (let ((cn (first sepSet)))  ; cutset node
          (dolist (colors cutsetColor)
            (let ((colorn (first colors)))  ; cutset node in color list
              (cond ((and (equal cn colorn) (not (null colorn)))
                 (setf cutset (cleanNeighbors cutset cn))
                 (setf cutsetColor (colorHelper cutset cutsetColor cn)))))))))

    (setf temp (separateTrees cutset))
    (dolist (n temp)
      (dolist (c cutsetcolor)
        (cond
          ((and (equal (first c) (first n)) (not (atom (second c))))
           (setf cutset (cleanneighbors cutset (first n)))
           (setf cutsetcolor (colorHelper cutset cutsetcolor (first n)))))))

    ;;separating the trees and setting them up for all possible colors
    (setf sepTrees (separateTrees treelist))

    ;;reset the cutset to hold all neighbors so you can remove possible
    ;;colors from the remaining trees needed to be colored
    (setf cutset nil)
    (dolist (c cutset-nodes)
      (dolist (s alist)
        (let ((n (first s))     ; node
              (adj (second s))) ; adjacent nodes
          (if (equal c n)
           (push (list c adj) cutset)))))

    ;;this is removing the cutset colors from the possible colors in their
    ;;neighboring nodes left to be colored.
    (dolist (c cutset)
      (dolist (neigh (second c))
        (dolist (pos treecolor)
          (if (equal (first pos) neigh)
             (dolist (cutc cutsetcolor)
               (if (equal (first c) (first cutc))
                  (setf (second pos) (remove (second cutc) (second pos)))))))))

    ;;rebuilding the trees so you can start at any node
    (setf temp1 nil)
    (dolist (n sepTrees)
      (setf temp1 (append temp1 (list (rebuildTree n treelist)))))

    ;;this resets the trees neighbors which was mangled in the rebuilding tree
    ;;function
    (dolist (n temp1)
      (dolist (tree n)
        (dolist (x treelist)
          (cond 
            ((equal (first tree) (first x))
             (setf (second tree) (second x)))))))
	
    ;;doing the coloring for each tree finding starting at the node that has the
    ;;least number of possible colors
    (setf sepTrees temp1)
    (dolist (n temp1)
      (setf temp1 nil)
      (setf temp 9999)
      (dolist (tree n)
        (dolist (c treecolor)
          (cond
            ((and (not (atom (second c)))
                  (equal (first c) (first tree))
                  (< (list-length (second c)) temp))
             (setf temp (list-length (second c)))
             (setf temp1 tree)))))
      (setf treelist (cleanneighbors treelist (first temp1)))
      (setf treecolor (colorHelper treelist treecolor (first temp1))))
	
    (append treeColor cutsetColor))) ; return two colorings together
	
;; Test driver
(defun coloring-test (maps)
  (let ((answer nil) (bogus nil))
    (dolist (alist maps)
      (setf answer (coloring (eval alist)))
      (debug-list (string alist) answer 0)
      (setf bogus (mapcan #'(lambda (x)
                              (if (null (member (second x) *colors*)) (list x)))
                          answer))
      (princ #\linefeed)
      (if (not (null bogus))
        (debug-list "ERRORS" bogus 0))
      (princ #\linefeed))))

(coloring-test (list 
                 '*australia*
             ;   '*11-states* 
             ;   '*15-states* 
             ;   '*23-states*
                 '*50-states*
                 'countries-map
               ))
