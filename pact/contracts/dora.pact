(namespace 'free)

; Governance token of the d-oracle.
; In include the following features:

; 1 - Special guards
; ------------------
; Two special guards are settable with the governance only
;   - Minting guard which limits minting capabilities (see 3)
;   - Slashing guard (see 4) which limits slashing capabilities
;
; The two guards are set using the governance function (set-special-guards)

; 2 - Locking
; -----------
; The contract manage 3 balances:
;    - an available balance
;    - a locked balance
;    - a total balance which is the sum of both.
;
; The locked balance has always an end-date. After this date, funds are released
; back to the available balance.
;
; The functions (lock-until) and (lock-for-duration). Theses two functions manage
; a total locked-balance
;      ie: if more were previously locked, or at later date they do nothing

; (update-locked-balance) is in charge of moving back a locked balance to the available
; one as soon as the lock period has elapsed.

; 3 - Minting / Burning
; ---------------------
;
; This token is mintable with the function (mint) and (mint-create). But this
; feature obviously guarded by the special guard to limit it to allowed contracts.
;   ie: Reserve contract which is the only one allowed to do token emission.
;
; The token is burnable. Each user is able to burn its tokens. He has although to
; be able to enforce the guard of its account/
;
; Burned/Minted (and thus in circulation) tokens count are stored in a table to keep
; statistics by chain.

; 4  - Multichain minting/burnng statistics
; -----------------------------------------
;
; The minting/burning statistics are transferable between chain using the defpact
; (transfer-minting-stats). This help to keep chains synchronized.
; Minting/burning stats are important to prepare future campaign of tokens
; emission/redemption.




(module dora GOVERNANCE

  (defconst VERSION "0.1")

  (implements fungible-v2)
  (implements fungible-xchain-v1)

  ;(use util.fungible-util)
  (use util.fungible-util)
  (use util.guards [enforce-before-date])
  (use util-math [sum min max])
  (use util-lists [replace-at extend-like])
  (use util-strings [to-string])
  (use util-time [genesis now latest is-past is-future to-time])

  ;; Basic administrative capabilities to upgrade and init the contract database

  (defconst LOCK-DATE:time (time "2024-01-01T00:00:00Z"))

  (defcap GOVERNANCE ()
    (enforce-before-date LOCK-DATE)
    (enforce-keyset "free.d-oracle-funders")
  )

  ; --------------------------------------------------------------------------
  ; Constants

  (defconst MINIMUM_PRECISION 12)
  ; --------------------------------------------------------------------------
  ; Schemas and Tables

  (defschema account-schema
    available-balance:decimal
    guard:guard
    locked-balance:decimal
    locked-time:time
  )

  (defschema special-guards-sch
    minter:guard
    slasher:guard
  )

  (defschema minting-stats-schema
      minted:[decimal]
      burnt:[decimal]
  )

  (deftable accounts-table:{account-schema})
  (deftable special-guards-table:{special-guards-sch})
  (deftable minting-stats-table:{minting-stats-schema})


  (defschema lock-info
    amount:decimal
    expire
  )

  ; --------------------------------------------------------------------------
  ; Capabilities
  (defcap DEBIT (sender:string)
    "Capability for managing debiting operations"
    (enforce-guard (at 'guard (read accounts-table sender)))
    (enforce (!= sender "") "valid sender"))

  (defcap CREDIT (receiver:string)
    "Capability for managing crediting operations"
    (enforce (!= receiver "") "valid receiver"))

  (defcap ROTATE (account:string)
    "Autonomously managed capability for guard rotation"
    @managed
    true)

  (defcap LOCK (account:string  lck:object{lock-info})
    @managed lck LOCK-manager
    (with-read accounts-table account {'guard:=g}
      (enforce-guard g))
  )

  (defun LOCK-manager:object{lock-info} (managed:object{lock-info} requested:object{lock-info})
    (bind managed {'amount:=m-amount, 'expire:=m-expire}
      (bind requested {'amount:=r-amount, 'expire:=r-expire}
          (enforce (<= r-amount m-amount) "Not enough capability to lock")
          (enforce (<= r-expire (to-time m-expire)) (format "Cannot lock to {}s" [r-expire]))
          managed))
  )

  (defcap TRANSFER:bool (sender:string receiver:string amount:decimal)
    "Capability for allowing transfers"
    @managed amount TRANSFER-mgr
    (enforce-valid-transfer sender receiver (precision) amount)
    (compose-capability (DEBIT sender))
    (compose-capability (CREDIT receiver))
  )

  (defun TRANSFER-mgr:decimal (managed:decimal requested:decimal)
    (let ((newbal (- managed requested)))
      (enforce (>= newbal 0.0) (format "Amount exceeded for {}" [(- newbal)]))
      newbal)
  )

  (defcap TRANSFER_XCHAIN:bool
    ( sender:string
      receiver:string
      amount:decimal
      target-chain:string
    )
    "Capability for allowing X-vhain transfers"
    @managed amount TRANSFER_XCHAIN-mgr
    (enforce-valid-transfer sender receiver (precision) amount)
    (compose-capability (DEBIT sender))
  )

  (defun TRANSFER_XCHAIN-mgr:decimal (managed:decimal requested:decimal)
    (enforce (>= managed requested)
      (format "TRANSFER_XCHAIN exceeded for balance {}" [managed]))
    0.0
  )

  (defcap TRANSFER_XCHAIN_RECD:bool
    ( sender:string
      receiver:string
      amount:decimal
      source-chain:string
    )
    @event true
  )

  (defcap MINTING_STATS_SENT (minted burnt dst-chain)
    @event
    true
  )

  (defcap MINTING_STATS_RECEIVED (minted burnt dst-chain)
    @event
    true
  )

  (defcap BURN (account:string amount:decimal)
    "Capability for allowing burning money"
    @managed amount TRANSFER-mgr
    (enforce-valid-account account)
    (enforce-valid-amount (precision) amount)
    (compose-capability (DEBIT account))
  )

  (defcap SET_SPECIAL_GUARDS ()
    "Capability for setting a minter"
    @event
    ;Only the governance can trust a new minter
    (compose-capability (GOVERNANCE))
  )

  (defcap INIT ()
    "Capability for init"
    @event
    (compose-capability (GOVERNANCE))
    (compose-capability (SET_SPECIAL_GUARDS))
  )

  (defcap TEST_ONLY ()
    "Internal capability for protecting test only functions... Must be never acquired"
    false
  )

  (defcap MINT (dest-account:string amount:decimal)
    @doc "Capability used by a minter"
    @managed amount TRANSFER-mgr
    ; Burning is only allowed on 1 chain
    (enforce-valid-account dest-account)
    (enforce-valid-amount (precision) amount)
    (with-read special-guards-table "" {'minter:=g}
      (enforce-guard g))
    (compose-capability (CREDIT dest-account))
  )

  (defcap SLASH (account:string amount:decimal)
    "Capability to slash an account"
    @managed amount TRANSFER-mgr
    (enforce-valid-account account)
    (enforce-valid-amount (precision) amount)
    (with-read special-guards-table "" {'slasher:=g}
      (enforce-guard g))
  )


  ; --------------------------------------------------------------------------
  ; Utility functions required by the fungible-v2 interface
  (defun create-account:string (account:string guard:guard)
    (enforce-valid-account account)
    (enforce-reserved account guard)

    (insert accounts-table account
      { 'available-balance: 0.0,
        'locked-balance: 0.0 ,
        'locked-time: (genesis),
        'guard: guard
      })
    (format "Account {} created" [account])
    )

  (defun get-balance:decimal (account:string)
    (with-read accounts-table account
               {'available-balance:= available,
                'locked-balance:= locked}
      (+ available locked))
  )

  (defun details:object{fungible-v2.account-details} (account:string)
    (with-read accounts-table account {'guard:= g}
      {'account: account,
       'balance: (get-balance account),
       'guard: g })
  )

  (defun rotate:string (account:string new-guard:guard)
    (with-capability (ROTATE account)
      (with-read accounts-table account {'guard:= old-guard }
        (enforce-guard old-guard)
        (update accounts-table account {'guard: new-guard})))
  )


  (defun precision:integer()
    MINIMUM_PRECISION)

  (defun enforce-unit:bool (amount:decimal)
     (enforce-precision (precision) amount))



  ;; Lock management
  ;-------------------------------------------------------------------------
  (defun update-locked-balance (account:string)
    (with-read accounts-table account
               {'available-balance:= available,
                'locked-balance:= locked,
                'locked-time:= _time}
      (if (and (> locked 0.0) (is-past _time))
          (update accounts-table account
                  {'available-balance: (+ available locked),
                   'locked-balance: 0.0,
                   'locked-time: (genesis)})
          false))
  )

  (defun get-locked-balance (account:string)
    (with-read accounts-table account
             {'locked-balance:= locked,
              'locked-time:= locked-time}
      (if (is-past locked-time) 0.0 locked))
  )


  (defun lock-until (account:string amount:decimal lock-time:time)
    @doc "Lock an amount until a time"
    (enforce (is-future lock-time) "Lock time must be in the future")
    (update-locked-balance account)
    (with-capability (LOCK account {'amount:amount, 'expire:lock-time})
      (with-read accounts-table account
               {'available-balance:= available,
                'locked-balance:= locked,
                'locked-time:= current-lock-time}
        (let* ((incremental-lock (max (- amount locked) 0.0))
               (lock-time-updated (latest current-lock-time lock-time)))
          (enforce (<= incremental-lock available) "Insufficient available")
          (update accounts-table account
                {'locked-balance: (+ locked incremental-lock),
                 'available-balance: (- available incremental-lock),
                 'locked-time: lock-time-updated
                }))))
  )

  (defun lock-for-duration (account:string amount:decimal duration:decimal)
    (enforce (> duration 0.0) "Lock time must be in the future")
    (lock-until account amount (add-time (now) duration))
  )

  ; --------------------------------------------------------------------------
  ; Transfer functions
  (defun transfer:string (sender:string receiver:string amount:decimal)
    (enforce-valid-transfer sender receiver (precision) amount)

    (with-capability (TRANSFER sender receiver amount)
      (debit sender amount)
      (with-read accounts-table receiver {'guard:= g}
        (credit receiver g amount)))
  )

  (defun transfer-create:string
    ( sender:string
      receiver:string
      receiver-guard:guard
      amount:decimal )

    (enforce-valid-transfer sender receiver MINIMUM_PRECISION amount)

    (with-capability (TRANSFER sender receiver amount)
      (debit sender amount)
      (credit receiver receiver-guard amount))
    )

  (defun debit:string (account:string amount:decimal)
    (require-capability (DEBIT account))
    (update-locked-balance account)
    (with-read accounts-table account {'available-balance:= balance}
      (enforce (<= amount balance) (format "Insufficient funds: {} available" [balance]))
      (update accounts-table account
              {'available-balance: (- balance amount)}))
  )



  (defun credit:string (account:string guard:guard amount:decimal)
    (require-capability (CREDIT account))
    ;(update-locked-balance account)
    (with-default-read accounts-table account
                       {'available-balance: -1.0,
                        'guard: guard,
                        'locked-balance: 0.0,
                        'locked-time: (genesis)}
                       { 'available-balance:= balance,
                         'guard:= retg,
                         'locked-balance:= locked-balance,
                         'locked-time:= locked-time}

      (enforce (= retg guard) "Account guards do not match")

      (let ((is-new (if (= balance -1.0)
                        (enforce-reserved account guard)
                        false)))
        (write accounts-table account
               {'available-balance: (if is-new amount (+ balance amount)),
                'guard: retg,
                'locked-balance: locked-balance,
                'locked-time: (genesis)})
                ))
  )



  (defschema crosschain-schema
    @doc "Schema for yielded value in cross-chain transfers"
    receiver:string
    receiver-guard:guard
    amount:decimal
    source-chain:string)

  (defpact transfer-crosschain:string
    ( sender:string
      receiver:string
      receiver-guard:guard
      target-chain:string
      amount:decimal )

    (step
      (with-capability
        (TRANSFER_XCHAIN sender receiver amount target-chain)

        (enforce (!= "" target-chain) "empty target-chain")
        (enforce (!= (at 'chain-id (chain-data)) target-chain)
          "cannot run cross-chain transfers to the same chain")


        ;; step 1 - debit delete-account on current chain
        (debit sender amount)
        (emit-event (TRANSFER sender "" amount))

        (let
          ((crosschain-details:object{crosschain-schema}
            { "receiver" : receiver
            , "receiver-guard" : receiver-guard
            , "amount" : amount
            , "source-chain" : (at 'chain-id (chain-data))
            }))
          (yield crosschain-details target-chain)
          )))

    (step
      (resume
        { "receiver" := receiver
        , "receiver-guard" := receiver-guard
        , "amount" := amount
        , "source-chain" := source-chain
        }

        (enforce (= target-chain (at 'chain-id (chain-data)))
          "Current chain id does not match the specified target chain for cross-chain transfer")

        (emit-event (TRANSFER "" receiver amount))
        (emit-event (TRANSFER_XCHAIN_RECD "" receiver amount source-chain))

        ;; step 2 - credit create account on target chain
        (with-capability (CREDIT receiver)
          (credit receiver receiver-guard amount))
        ))
    )

    ; --------------------------------------------------------------------------
    ; Minting/burning functions
  (defun --chain-id:integer ()
    @doc "Return the chain id as an integer"
    (str-to-int 10 (at 'chain-id (chain-data)))
  )

  (defun --list-cumul:[decimal] (in:[decimal] value:decimal)
    @doc "Add a value to a table: where the index is the chain-id"
    (let ((idx (--chain-id)))
      (replace-at in idx (+ value (at idx in))))
  )


  (defun mint (account-name:string amount:decimal)
    @doc "Mint an amount of token. Can only be called by a registered minter and the (MINT ..) capability"
    (let ((guard (at 'guard (details account-name))))
      (mint-create account-name guard amount))
  )

  (defun mint-create (account-name:string guard:guard amount:decimal)
    @doc "Mint an amount of token. Can only be called by a registered minter and the (MINT ..) capability"
    (with-capability (MINT account-name amount)
      (credit account-name guard amount)
      (with-read minting-stats-table "" {"minted":=x}
        (update minting-stats-table "" {"minted": (--list-cumul x amount)})
        (concat [(to-string amount) " minted for " account-name]))
  ))

  (defun burn:string (account-name:string amount:decimal)
    @doc "Burn an amount of tokens: can be called by anyone with the proper guard and the (BURN ...) capability"
    (with-capability (BURN account-name amount)
      (debit account-name amount)
      (with-read minting-stats-table "" {"burnt":=x}
        (update minting-stats-table "" {"burnt": (--list-cumul x amount)})
        (concat [(to-string amount) " burnt for " account-name]))
  ))

  (defun slash:string (account:string total-amount:decimal slasher-account:string slasher-reward:decimal)
    @doc "Slash a bad actor \
          \  - The total amount is removed from his account \
          \  - Optionally a  slasher may receive one part is this amount (slasher-account / slasher-reward) \
          \  - The difference is burnt"
    (with-capability (SLASH account total-amount)
      (update-locked-balance account)
      (with-read accounts-table account {'locked-balance:= locked-bal}
        (let* ((slash-amount (min total-amount locked-bal))
               (to-burn (- slash-amount slasher-reward)))
          (enforce (> to-burn 0.0) "Burned amount must be positive")
          (enforce (> slash-amount 0.0) "Slash amount must be positive")

          ; Remove the slash-amount from the slashed
          (update accounts-table account {'locked-balance: (- locked-bal slash-amount)})

          ; If there is a slasher, increment it's balance by slasher-reward
          (if (> slasher-reward 0.0)
              (with-read accounts-table slasher-account {'guard:= g}
                (credit slasher-account g slasher-reward))
              "")

          ; Mark the difference value as burnt
          (with-read minting-stats-table "" {"burnt":=x}
            (update minting-stats-table "" {"burnt": (--list-cumul x to-burn)}))
          (concat [(to-string slash-amount) " slashed for " account])))
  ))



  ;;; -------------------------------------------------------------------------
  ;;; MINTING STATS
  ;;; -------------------------------------------------------------------------
  (defun get-minting-stats:{minting-stats-schema} ()
    @doc "Returns minting/burning stats"
    (read minting-stats-table ""))

  ; This function can't be used only in REPL for testing.
  ; It is guarded by the TEST_ONLY cap, which can be acquired outside the REPL
  (defun force-mint-burn-stats (stats:object{minting-stats-schema})
    (require-capability (TEST_ONLY))
    (update minting-stats-table "" stats)
  )


  (defun total-minted:decimal ()
    @doc "Returns the amount of minted tokens"
      (with-read minting-stats-table "" {"minted":=x}
        (sum x))
  )

  (defun total-burnt:decimal ()
    @doc "Returns the amount of burnt tokens"
      (with-read minting-stats-table "" {"burnt":=x}
        (sum x))
  )

  (defun total-supply:decimal ()
    @doc "Returns the amount of circulating tokens"
    (- (total-minted) (total-burnt))
  )

  (defpact transfer-minting-stats:string (target-chain)
    @doc "Pact to transfer minting stats to others chains"
    (step
      (with-read minting-stats-table "" {"minted":=minted, "burnt":=burnt}
        (emit-event (MINTING_STATS_SENT minted burnt target-chain))
        (yield  {"m":minted, "b":burnt} target-chain)))

    (step
      (resume {"m" := rec-minted, "b" := rec-burnt}
        (emit-event (MINTING_STATS_RECEIVED rec-minted rec-burnt (at 'chain-id (chain-data))))
        (with-read minting-stats-table "" {"minted":=minted, "burnt":=burnt}
          (update minting-stats-table ""
            { "minted": (zip (max) rec-minted (extend-like minted rec-minted 0.0)),
              "burnt":  (zip (max) rec-burnt (extend-like burnt rec-burnt 0.0))
            }))))
  )

;;; -------------------------------------------------------------------------
;;; MINTING / SLASHING GUARDS
;;; -------------------------------------------------------------------------
  (defun --default-not-allowed:bool ()
    (enforce false "Minting or Slashing not allowed"))

  (defconst DEFAULT-NOT-ALLOWED-GUARD:guard (create-user-guard (--default-not-allowed)))

  (defun --set-special-guards:string (minter:guard slasher:guard)
    @doc "Private function to set special guards"
    (require-capability (SET_SPECIAL_GUARDS))
    (write special-guards-table ""
      { 'minter:minter, 'slasher:slasher})
    "Special guards update successful"
  )

  (defun set-special-guards:string (minter:guard slasher:guard)
    @doc "Function to set the guards for minting and slashing. \
          \ Can only be called by gouvernance"
    (with-capability (SET_SPECIAL_GUARDS)
      (--set-special-guards minter slasher))
  )

  (defun init:string ()
    (with-capability (INIT)
      (let ((empty (make-list (+ (--chain-id) 1) 0.0)))
        (insert minting-stats-table "" {"minted": empty, "burnt":empty}))
      (let ((g DEFAULT-NOT-ALLOWED-GUARD))
        (--set-special-guards g g)))
    "Contract initialized"
  )
)
