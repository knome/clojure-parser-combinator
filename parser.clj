
;; Combinatorial Parser Generator

(ns parser)

(defstruct parser-state
  :tokens :ast)

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
           (struct-map parser-state
             :tokens (:tokens ~last-var)
             :ast    (do ~@ast)))) ]))

(defn is-a [ pf ] ; predicate function
  [ (fn [ state ]
      (when (and (:tokens state)
                 (pf (first (:tokens state))))
        [ (struct-map parser-state
            :tokens (rest (:tokens state))
            :ast    (first (:tokens state))) ])) ])

(defn either [ & fns ]
  (reduce concat fns))

(defn verifying [ & pfns ] ; stand alone predicate functions , not given a token
  [ (fn [ state ]
      (when (every? apply pfns)
        [state]))])

(defn run-all [ parser tokens ]
  (for [parser-func parser
        state       (parser-func {:tokens tokens})]
    state))

(defn run [ parser tokens ]
  (first (run-all parser tokens)))

(defn matches-all? [ parser tokens ]
  (let [m (run parser tokens)]
    (and m (not (:tokens m)))))

;; applies the given parser extracting an ast, but leaves the tokens in-place
(defn peeking [ parser ]
  [ (fn [ state ]
      (let [peek-state (and (:tokens state)
                            (run parser (:tokens state)))]
        [ (struct-map parser-state
            :tokens (:tokens state)
            :ast    (:ast peek-state)) ])) ])
  
;; (repeating :at-least 1 :up-to 10 parse-fn)
;; (repeating #(= 5 %))
;; (repeating :interleaving parse-fn parse-fn) ; interleaved values are not captured , if they ought to be do not use this
;; (repeating :exactly 3 parse-fn)
;; (repeating :greedy :less parse-fn)
;; (repeating :collecting :all parse-fn) ; as opposed to the default of :collecting :first ; that is, either match the most ( or least dependant on greediness ) or nothing, not partials/extensions
;; the last thing is the list of functions to chain the state into
;; everything upto there is dropped into a hash

(defmacro repeating [ & opts-then-fnlist ]
  (let [opts (apply hash-map (take (+ -1 (count opts-then-fnlist)) opts-then-fnlist))
        ifns  (last opts-then-fnlist)]
    ;; may specify either an :exactly count of expected repititions, or both, either or neither of :at-least and :up-to counts
    (assert (or (and (or (:at-least opts)
                         (:up-to    opts))
                     (not (:exactly opts)))
                (and (not (or (:at-least opts)
                              (:up-to    opts)))
                     (:exactly opts))
                (and (not (or (:at-least opts)
                              (:up-to    opts)
                              (:exactly  opts))))))
    ;; matches at minimum the specified number of matches
    (assert (or (not (:at-least opts))
                (not (:up-to    opts))
                (>= (:up-to opts)
                    (:at-least opts))))
    ;; the repitition has a :greedy setting of either :more * or :less *?
    (assert (or (not (:greedy opts))
                (= :more (:greedy opts))
                (= :less (:greedy opts))))
    ; different combinations of options will render into different code segments diverging here
    (or (and (:exactly opts) ; if there is an exact amount given greediness is irrelevant
             (let [vars (take (:exactly opts) (repeatedly gensym))]
               `(whereas [ ~@(reduce concat (let [uiv (map (fn [v#] (list v# ifns)) vars) ]
                                              (if (:interleaving opts)
                                                (interpose (list (gensym) (:interleaving opts)) uiv)
                                                uiv)))]
                         [~@vars])))
        ; start a surrounding whereas , if there is a minimum put it here with an exact
        ; after that insert a parse-function that will act appropriate to the greediness or lack thereof in the repeats option set
        (let [depth-var         (gensym)
              deeper-values-var (gensym)
              initial-state-var (gensym)
              depthfully-gather-var (gensym)]
          `[ (fn ~depthfully-gather-var
               ( [ ~initial-state-var ]
                   ( ~@(if (= (:collecting opts) :all)
                         `(do)
                         `((comp list first)))
                     (~depthfully-gather-var
                      {:tokens (:tokens ~initial-state-var) :ast []}
                      0) ))
               ( [ ~initial-state-var ~depth-var ]
                   ;; wrap the body in either an if statement checking the current valuation depth or a do depending on need
                   ( ~@(if (:up-to opts)
                         `(if (< ~(:up-to opts) ~depth-var) nil)
                         `(do))
                     (if-let [~deeper-values-var (map 
                                                  (fn [s#]
                                                    {:tokens (:tokens s#)
                                                     :ast (concat (:ast ~initial-state-var) [ (:ast s#) ])})
                                                  (reduce concat (map (fn [ifn#] (ifn# ~initial-state-var))
                                                                      ~(if (:interleaving opts)
                                                                         `(if (= ~depth-var 0)
                                                                            ~ifns
                                                                            (whereas [_# ~(:interleaving opts)
                                                                                      v# ~ifns ]
                                                                                     v#))
                                                                         ifns))))]
                       (reduce concat
                               (reduce concat 
                                       [ ~@(when (= (:greedy opts) :less)
                                             (if (:at-least opts)
                                               `((if (> ~(:at-least opts) ~depth-var) [] [ [ [ ~initial-state-var ] ] ]))
                                               `[ [ [ ~initial-state-var ] ] ]))
                                         (map (fn [ns#] (~depthfully-gather-var ns# (inc ~depth-var))) ~deeper-values-var) 
                                         ~@(when (not (= (:greedy opts) :less))
                                             (if (:at-least opts)
                                               `((if (> ~(:at-least opts) ~depth-var) [] [ [ [ ~initial-state-var ] ] ]))
                                               `[ [ [ ~initial-state-var ] ] ])) ]))
                       ~(if (:at-least opts)
                          `(if (> ~(:at-least opts) ~depth-var) [] [ ~initial-state-var ])
                          `[ ~initial-state-var ]))))) ]))))
