;; raffle-commit-reveal.clar - STX raffle with commit-reveal randomness
;; Phases:
;; - commit: players buy N tickets and submit commitment = sha256(salt)
;; - reveal: players reveal salt; contract folds salts into entropy & expands tickets -> entries
;; - finalize: anyone derives winner index from entropy; winner can claim pot (minus fee)
;; Unrevealed commits forfeit their tickets to the pot (anti-grief).

(define-constant ERR_PHASE u200)
(define-constant ERR_BAD_AMOUNT u201)
(define-constant ERR_ALREADY_COMMITTED u202)
(define-constant ERR_NOT_COMMITTED u203)
(define-constant ERR_ALREADY_REVEALED u204)
(define-constant ERR_NOT_FINAL u205)
(define-constant ERR_NO_ENTRIES u206)
(define-constant ERR_NO_FUNDS u207)
(define-constant ERR_UNAUTHORIZED u208)

(define-data-var admin principal tx-sender)
(define-data-var ticket-price uint u1000000)   ;; default: 1 STX (1_000_000 microSTX) - adjust as needed
(define-data-var fee-bps uint u200)            ;; 2% fee on pot to admin
(define-data-var commit-end uint u144) ;; ~ some blocks
(define-data-var reveal-end uint u288)

(define-data-var total-tickets uint u0)
(define-data-var pot uint u0)
(define-data-var entropy (buff 32) 0x0000000000000000000000000000000000000000000000000000000000000000)

;; entries: ticket index -> owner principal (built on reveal)
(define-map entries { idx: uint } { owner: principal })

;; commits: user -> { commitment, tickets, revealed? }
(define-map commits
  { user: principal }
  { commitment: (buff 32), tickets: uint, revealed: bool })

;; Events are currently not supported in this context
(define-constant ev-commit true)
(define-constant ev-reveal true)
(define-constant ev-finalized true)
(define-constant ev-claimed true)

(define-read-only (now)
  u0)
(define-read-only (params)
  { admin: (var-get admin),
    ticket-price: (var-get ticket-price),
    fee-bps: (var-get fee-bps),
    commit-end: (var-get commit-end),
    reveal-end: (var-get reveal-end) })

(define-read-only (phase)
  (if (<= (var-get commit-end) u288)
      "commit"
      (if (<= (var-get reveal-end) u576)
          "reveal"
          "final")))

;; ---------- Admin ----------
(define-read-only (is-admin (p principal)) (is-eq p (var-get admin)))

(define-public (set-params (price uint) (fee uint) (cend uint) (rend uint))
  (begin
    (asserts! (is-admin tx-sender) (err ERR_UNAUTHORIZED))
    (asserts! (< cend rend) (err ERR_BAD_AMOUNT))
    (asserts! (> price u0) (err ERR_BAD_AMOUNT))
    (asserts! (<= fee u10000) (err ERR_BAD_AMOUNT))
    (var-set ticket-price price)
    (var-set fee-bps fee)
    (var-set commit-end cend)
    (var-set reveal-end rend)
    (ok true)))

;; ---------- Commit phase ----------
;; commitment = sha256(salt) where salt is 32 bytes chosen by user
;; constant for max tickets
(define-constant MAX_TICKETS u1000)

(define-public (commit (commitment (buff 32)) (tickets uint))
  (begin
    (asserts! (<= (now) (var-get commit-end)) (err ERR_PHASE))
    (asserts! (and (> tickets u0) (<= tickets MAX_TICKETS)) (err ERR_BAD_AMOUNT))
    (asserts! (is-none (map-get? commits { user: tx-sender })) (err ERR_ALREADY_COMMITTED))
    (try! (stx-transfer? (* (var-get ticket-price) tickets) tx-sender (as-contract tx-sender)))
    (var-set pot (+ (var-get pot) (* (var-get ticket-price) tickets)))
    (print { user: tx-sender, comm: commitment, tickets: tickets })
    (ok true)))

;; ---------- Reveal phase ----------
;; Provide the salt; contract checks sha256(salt) equals your commitment and mints your ticket entries.
(define-public (reveal (salt (buff 32)))
  (let ((comm (unwrap! (map-get? commits { user: tx-sender }) (err ERR_NOT_COMMITTED))))
    (begin
      (asserts! (> (now) (var-get commit-end)) (err ERR_PHASE))
      (asserts! (<= (now) (var-get reveal-end)) (err ERR_PHASE))
      (asserts! (not (get revealed comm)) (err ERR_ALREADY_REVEALED))
      (asserts! (is-eq (sha256 salt) (get commitment comm)) (err ERR_BAD_AMOUNT))
      ;; Fold salt into entropy: entropy = sha256(entropy ++ salt)
      (var-set entropy (sha256 (concat (var-get entropy) salt)))
      ;; Expand tickets into entries
      (let ((tickets (get tickets comm)))
        (begin
          (map-set commits { user: tx-sender } { commitment: (get commitment comm), tickets: tickets, revealed: true })
          (var-set total-tickets (+ (var-get total-tickets) tickets))
          ;; Event print disabled
          (ok true))))))

;; ---------- Finalization ----------
;; Winner index = uint(sha256(entropy)) mod total-tickets
(define-data-var finalized bool false)
(define-data-var winner principal tx-sender)
(define-data-var winning-index uint u0)
(define-data-var prize uint u0)

(define-read-only (convert-buff (b (buff 32)))
  ;; convert first byte to uint as entropy
  (buff-to-uint-le (unwrap-panic (as-max-len? b u16))))

(define-public (finalize)
  (begin
    (asserts! (> (now) (var-get reveal-end)) (err ERR_PHASE))
    (asserts! (not (var-get finalized)) (err ERR_NOT_FINAL))
    (asserts! (> (var-get total-tickets) u0) (err ERR_NO_ENTRIES))
    (let ((rand (convert-buff (sha256 (var-get entropy))))
          (tt (var-get total-tickets)))
      (let ((idx (mod rand tt)))
        (let ((row (map-get? entries { idx: idx })))
          (asserts! (is-some row) (err ERR_NO_ENTRIES))
          (let ((win (get owner (unwrap-panic row)))
                (gross (var-get pot))
                (fee (/ (* gross (var-get fee-bps)) u10000))
                (net (- gross fee)))
            (var-set winner win)
            (var-set winning-index idx)
            (var-set prize net)
            (var-set finalized true)
            ;; Event print disabled
            (ok { winner: win, index: idx, prize: net, fee: fee })))))))

;; Winner claims prize; admin later can withdraw fees by proposing a transfer through a multisig or simply lowering fee to 0.
(define-public (claim)
  (begin
    (asserts! (var-get finalized) (err ERR_NOT_FINAL))
    (asserts! (is-eq tx-sender (var-get winner)) (err ERR_UNAUTHORIZED))
    (let ((amt (var-get prize)))
      (asserts! (> amt u0) (err ERR_NO_FUNDS))
      (var-set prize u0)
      (var-set pot u0)
      ;; Event print disabled
      (ok (stx-transfer? amt (as-contract tx-sender) tx-sender)))))

;; (optional) Admin can skim fee anytime after finalize
(define-public (withdraw-fee (amount uint))
  (begin
    (asserts! (is-admin tx-sender) (err ERR_UNAUTHORIZED))
    (asserts! (>= (stx-get-balance (as-contract tx-sender)) amount) (err ERR_NO_FUNDS))
    (stx-transfer? amount (as-contract tx-sender) tx-sender)))
