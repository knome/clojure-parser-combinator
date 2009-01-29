
;; Combinatorial Parser Generator

(ns parser)

(defstruct parser-state
  :tokens :ast)

(defn- win [ & args ]
  (apply struct-map parser-state args))

(defn- per 
  "transform a sequence into a sequence of n-tuples; does not verify length, if not multiple of n returns partial sequence last"
  [ n s ]
  (when s
    (lazy-cons
     (take n s)
     (per n (drop n s)))))

(defmacro whereas [ [ & vs ] & ast ]
  (let [initial-state-var (gensym) 
        [ for-statements last-var ] (loop [vars-left      (per 2 vs)
                                           for-statements '() 
                                           last-var       initial-state-var]
                                      (if (nil? vars-left)
                                        [for-statements
                                         last-var ]
                                        (let [ [n v] (first vars-left)   ; [ name variable-binding-statement ]
                                               nv    (gensym)          ] ; new-variable
                                          (recur
                                           (rest vars-left)
                                           (concat for-statements `(~nv (reduce concat (map (fn [s#] (s# ~last-var)) ~v)) ~n [ (:ast ~nv) ] :when ~nv ))
                                           nv)))) ]
    `[ (fn [ ~initial-state-var ]
         (for [ ~@for-statements ]
           (win :tokens (:tokens ~last-var)
                :ast    (do ~@ast)))) ]))

(defn is-a [ pf ] ; predicate function
  [ (fn [ state ]
      (when (pf (first (:tokens state)))
        [ (win :tokens (rest (:tokens state))
               :ast    (first (:tokens state))) ])) ])

(defn either [ & fns ]
  (reduce concat fns))

(defn verifying [ & pfns ] ; stand alone predicate functions , not given a token
  [ (fn [ state ]
      (when (every? apply pfns)
        [state]))])

(defn- intersperse [ v ls ]
  (lazy-cons
   (first ls)
   (reduce concat (map #(list v %) (rest ls)))))

(defn run [ parser token ]
  (first (for [parser-func parser
               state       (parser-func token)]
           state)))

;; (repeating :at-least 1 :up-to 10 parse-fn)
;; (repeating #(= 5 %))
;; (repeating :interleaving parse-fn parse-fn) ; interleaved values are not captured , if they are do not use this
;; (repeating :exactly 3 parse-fn)
;; (repeating :greedy :less parse-fn)
;; the last thing is the list of functions to chain the state into
;; everything upto there is dropped into a hash

(defmacro repeating [ & opts-then-fnlist ]
  (let [opts (apply hash-map (take (+ -1 (count opts-then-fnlist)) opts-then-fnlist))
        ifns  (last opts-then-fnlist)]
    (assert (or (and (or (:at-least opts)
                         (:up-to    opts))
                     (not (:exactly opts)))
                (and (not (or (:at-least opts)
                              (:up-to    opts)))
                     (:exactly opts))
                (and (not (or (:at-least opts)
                              (:up-to    opts)
                              (:exactly  opts))))))
    (assert (or (not (:at-least opts))
                (not (:up-to    opts))
                (>= (:up-to opts)
                    (:at-least opts))))
    (assert (or (not (:greedy opts))
                (= :more (:greedy opts))
                (= :less (:greedy opts))))
    ; different combinations of options will render into different code segments diverging here
    (or (and (:exactly opts) ; if there is an exact amount given greediness is irrelevant
             (let [vars (take (:exactly opts) (repeatedly gensym))]
               `(whereas [ ~@(reduce concat (let [uiv (map (fn [v#] (list v# ifns)) vars) ]
                                              (if (:interleaving opts)
                                                (intersperse (list (gensym) (:interleaving opts)) uiv)
                                                uiv)))]
                         [~@vars])))
        ; start a surrounding whereas , if there is a minimum put it here with an exact
        ; after that insert a parse-function that will act appropriate to the greediness or lack thereof in the repeats option set
        (let [vars (take (or (:at-least opts) 0) (repeatedly gensym))
              rvar (gensym)]
          `(whereas [~@(reduce concat (let [uiv (map (fn [v#] (list v# ifns)) vars) ]
                                        (if (:interleaving opts)
                                          (intersperse (list (gensym) (:interleaving opts)) uiv)
                                          uiv)))
                     ~@(when (and (:at-least opts) (:interleaving opts))
                         (list (gensym) (:interleaving opts)))
                     ~rvar (either ~(or (and true ; if we are processing repitition , no interleaving , no up-to ; yet
                                             (= :less (:greedy opts))
                                             ;; non-greedy
                                             `[ (fn [ initial-state# ]
                                                  ((fn depthfully-gathering# [ state# ] 
                                                     (when-let [deeper-states# (map
                                                                                (fn [s#]
                                                                                  {:tokens (:tokens s#) :ast [(:ast s#)]})
                                                                                (reduce concat (map 
                                                                                                (fn [ifn#]
                                                                                                  (ifn# state#))
                                                                                                ~ifns)))]
                                                       (map 
                                                        (fn [s#]
                                                          {:tokens (:tokens s#)
                                                           :ast (vec (reduce concat [(:ast state#) (:ast s#)]))})
                                                        (reduce concat (map 
                                                                        (fn [s#]
                                                                          (concat [ s# ] (depthfully-gathering# s#)))
                                                                        deeper-states#)))))
                                                   {:tokens (:tokens initial-state#) :ast []}))])
                                        ;; greedy
                                        `[ (fn [ initial-state# ]
                                             ((fn depthfully-gathering# [ state# ] 
                                                (when-let [deeper-states# (map
                                                                           (fn [s#]
                                                                             {:tokens (:tokens s#) :ast [(:ast s#)]})
                                                                           (reduce concat (map 
                                                                                           (fn [ifn#]
                                                                                             (ifn# state#))
                                                                                           ~ifns)))]
                                                  (map 
                                                   (fn [s#]
                                                     {:tokens (:tokens s#)
                                                      :ast (vec (reduce concat [(:ast state#) (:ast s#)]))})
                                                   (reduce concat (map 
                                                                   (fn [s#]
                                                                     (concat (depthfully-gathering# s#) [ s# ]))
                                                           deeper-states#)))))
                                              {:tokens (:tokens initial-state#) :ast []}))])
                                   ; this causes nested 0 allowing repeats to overflow
                                   ; so a symbol representing ran but did nothing will need to be devised
                                   ; perhaps consumption tracking?
                                   ; specifically (run (repeating (either (repeating (is-a #(= 1 %))) (is-a #(= 2 %)))) {:tokens [3]})
                                   ; specifically (run (repeating (either (repeating :at-least 1 (is-a #(= 1 %))) (is-a #(= 2 %)))) {:tokens [1 1 1 2 1 1 2]})
                                   ; this should not be a problem in most actually grammars
                                   [ (fn [ s# ] [{:tokens (:tokens s#) :ast nil}])])]
                    (concat [ ~@vars ] ~rvar ))))))