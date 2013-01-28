(ns ui.core
  (:require
    [hlisp.env :as hl]
    )
  (:use
    [flapjax.core   :only [oneE zeroE mapE mergeE switchE filterE constantE
                           collectE notE filterRepeatsE receiverE sendE
                           snapshotE onceE skipFirstE delayE blindE calmE
                           timerE valueNow switchB andB orB notB liftB condB
                           ifB timerB blindB calmB isE? isB? E->B B->E initE
                           doE consE applyE caseE constantB delayB consB applyB
                           compE onClickE onChangeE onMouseDownE onMouseUpE
                           onMouseOverE onMouseOutE onHoverE onActiveE domAttr
                           domRemoveAttr domCss domAddClass domRemoveClass
                           domToggleClass domToggle domSlideToggle domText
                           domValue domValueB doInitE onDblClickE onSubmitE]]
    [flapjax.dom    :only [id! add-class! dom-get value!]]))

(def trans
  "Matrix transpose."
  (partial apply map vector))

(defn make-input
  ([e] 
   (let [b     (when (isB? e) e)
         e     (id! (if (isB? e) hl/input e))
         inE   (receiverE)
         outB  (or b (E->B (mergeE (doInitE #(value! e)) (onChangeE e) inE)))]
     (mapE #(value! e %) inE)
     {:elem e
      :valE inE
      :valB outB}))
  ([e inB]
   (let [in (make-input e)]
     (assoc in :elem (domValue (:elem in) (B->E inB))))))

(defn make-binary-state
  [dflE adjective state-true state-false]  
  (fn binary
    ([e]
     (let [e (id! e)]
       (binary e (dflE e))))
    ([e streamE]
     (let [e (id! e)]
       (-> e
         (domAddClass (initE adjective))
         (domAttr (consE (constantE streamE (str "data-" state-true)) streamE))
         (domToggleClass (consE (constantE streamE state-true) streamE))
         (domToggleClass (consE (constantE streamE state-false) (notE streamE))))))))

(defn make-multi-state
  [e streamE & pred-classes]
  (let [e (id! e)]
    (mapv
      (fn [[pred clas]]
        (let [clasE (constantE streamE clas)
              predE (mapE #(pred %) streamE)]
          (domToggleClass e (consE clasE predE))))
      (partition 2 pred-classes)) 
    e))

(def make-hoverable
  "Hoverable elements have the 'hover' class on them whenever the mouse is
  over them."
  (make-binary-state onHoverE "hoverable" "hover" "not-hover"))

(def make-clickable
  "Clickable elements have the 'active' class applied whenever the mouse is
  pressed on them."
  (make-binary-state onActiveE "clickable" "active" "not-active"))

(def make-selectable
  "Selectable elements..."
  (make-binary-state onClickE "selectable" "selected" "not-selected"))

(def make-disableable
  "Disableable elements..."
  (make-binary-state zeroE "disableable" "disabled" "not-disabled"))

(def make-checkable
  "Checkable elements..."
  (make-binary-state onClickE "checkable" "checked" "not-checked"))

(defn make-global-message
  [e msg-e hide-e]
  (let [showE   (receiverE)
        shownB  (E->B showE ::nil)
        e       (id! e)
        msg-e   (id! msg-e)
        hide-e  (id! hide-e)]
    (-> e
      (domToggleClass (consE (constantE showE "error") (mapE #(= :error (first %)) showE)))
      (domToggleClass (consE (constantE showE "warning") (mapE #(= :warning (first %)) showE)))
      (domToggleClass (consE (constantE showE "notice") (mapE #(= :notice (first %)) showE)))
      (domSlideToggle (mapE second showE)))
    (domText msg-e (mapE #(if % % "") (mapE second showE)))
    (mapE #(sendE showE [false false]) (onClickE hide-e))
    {:elem      e
     :msg-elem  msg-e
     :hide-elem hide-e
     :showE     showE
     :shownB    shownB}))

(defn make-checkbox
  "A checkbox is..."
  [e]
  (let [checkE    (receiverE)
        checkedB  (E->B checkE ::nil)
        e         (-> e
                    (make-checkable checkE)
                    make-clickable
                    make-hoverable)]
    (mapE #(sendE checkE ((if % not identity) (valueNow checkedB)))
          (onClickE e))
    {:elem      e
     :checkE    checkE
     :checkedB  checkedB}))

(defn make-deck
  "A deck is..."
  [& optvals]
  (let [[options values] (apply map vector (partition 2 optvals))
        selectE   (receiverE)
        selectedB (E->B selectE ::nil)
        wireup    (fn [e v] (make-selectable e (mapE #(= v %) selectE)))]
    {:selectE   selectE
     :selectedB selectedB
     :options   (mapv wireup options values)
     :values    values}))

(defn make-deck2
  "A deck is..."
  [inB & optvals]
  (let [[options values] (apply map vector (partition 2 optvals))
        wireup    (fn [e v] (make-selectable e (mapE #(= v %) (B->E inB))))]
    {:options   (mapv wireup options values)
     :values    values}))

(defn- make-select-by
  "A select is..."
  [f & optvals]
  (let [deck    (apply make-deck optvals)
        wireup  (fn [e v]
                  (mapE #(sendE (:selectE deck) v) (f e))
                  (-> e make-clickable make-hoverable))]
    (assoc deck :options (mapv wireup (:options deck) (:values deck)))))

(defn make-select
  "A select is..."
  [& optvals]
  (apply make-select-by onClickE optvals))

(defn make-select-dblclick
  "A select is..."
  [& optvals]
  (apply make-select-by onDblClickE optvals))

(defn make-restricted-select
  [select]
  (let [restrictE (receiverE)]
    (mapv (fn [e v] (make-disableable e (mapE #(contains? % v) restrictE)))
          (:options select)
          (:values select))
    (assoc select :restrictE restrictE :restrictedB (E->B restrictE #{}))))

(defn link-unique-selects
  [& selects]
  (let [linkedB (apply consB (mapv :selectedB selects))
        linkedE (receiverE)
        rset    #(set (concat (take %1 %2) (drop (inc %1) %2)))]
    (doall
      (map-indexed
        (fn [i e]
          (mapE #(sendE (:selectE e) (nth % i)) linkedE)
          (mapE #(sendE (:restrictE e) (rset i %)) (B->E linkedB)))
        selects)) 
    {:linkedE linkedE
     :linkedB linkedB
     :selects selects}))

(defn make-linked-selects
  [n & optvals]
  (let [selects (mapv #(apply make-select optvals) (range 0 n))]
    (apply link-unique-selects (mapv make-restricted-select selects))))

(defn make-tabs
  [& optvals]
  (let [[options containers values] (apply map vector (partition 3 optvals))
        select  (apply make-select (interleave options values))
        deck    (apply make-deck (interleave containers values))]
    (mapE #(sendE (:selectE deck) %) (B->E (:selectedB select)))
    (assoc select :containers (:options deck))))

(defn make-form
  "Wire up a form to call a function with arguments supplied by the form's
  input elements when the form is submitted."
  [f form & inputs]
  (let [form      (id! form)
        trigE     (onSubmitE form)
        [es bs]   (trans (map (comp (juxt :elem :valB) make-input) inputs)) 
        argB      (apply liftB vector bs)
        argE      (mapE (fn [_] (valueNow argB)) trigE)]
    (mapE (partial apply f) argE)
    {:form    form
     :inputs  es}))

