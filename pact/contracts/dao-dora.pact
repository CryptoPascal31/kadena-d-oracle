(namespace 'free)

(module dao-dora UPGRADE-CONTRACT
  (defconst VERSION "0.1")

  (use free.util-strings [upper])
  (use util.guards1)
  (use free.util-time [now is-future is-past])
  (use free.util-math [sum3])


  (defconst INITIAL-GOVERNOR-LOOSE-POWER:time (time "2023-06-01T00:01:00Z"))

  (defconst INITIAL-GOVERNOR-GUARD:guard (keyset-ref-guard  "free.dora-initial-governor"))

  (defcap APPROVED-BY-DAO ()
    (if (and (is-future INITIAL-GOVERNOR-LOOSE-POWER)
             (try-enforce-guard INITIAL-GOVERNOR-GUARD))
        true
        (enforce-approve-transaction))
  )

  (defcap APPROVED-BY-GOVERNOR ()
    (approve-transaction-by-governor)
  )


  (defcap UPGRADE-CONTRACT ()
    (compose-capability (APPROVED-BY-DAO))
  )

  (defcap PROPOSE (description:string hash:string)
    @event
    (compose-capability (APPROVED-BY-GOVERNOR))
  )


  (defcap VOTE (account-name:string)
    @managed
    (let ((guard (at 'guard (free.dora.details account-name))))
      (enforce-guard guard))
  )

  (defconst PROPOSAL-VOTING-TIME (days 14))
  (defconst PROPOSAL-ACTION-TIME (days 21))
  (defconst EXTRA-LOCKING-TIME (hours 1))

  ; Represents a proposal to be voted
  (defschema proposal
    id:integer  ;ID of the proposal: Integer #0, #1 #2n ...
    description:string ;Description
    hash:string ;Hash of the proposal transaction
    transaction-data:string ;Full string of the transaction
    end-time:time ;When the voting period ends
    action-time:time ;When the submission of the voted transaction ends
    validated:bool ; True is the transaction has been done.
    yes:decimal ; Count of Yes votes
    no:decimal ; Count of No votes
    neutral:decimal ;Count of neutral votes
    count:integer ; Count the number of votes (for information)
  )

  (defschema governor
    name:string ; Governor name => Only for information
    enabled:bool ;false is the governor has been revoked, true otherwise
    guard:guard ; Guard of the governor
  )

  ; TODO Change name
  (defschema voter
    voted:bool
  )

  ; IDs of proposal storage
  (defschema proposal-id
    id:integer
  )

  (deftable governors-tab:{governor})
  (deftable proposal-id-tab:{proposal-id})
  (deftable proposal-tab:{proposal})
  (deftable voter-tab:{voter})

  (defun add-governor (governor-name:string guard:guard)
    @doc "Add a governor to the DAO => Need a vote"
    ; Adding a governor is only allowed by a full DAO vote
    (with-capability (APPROVED-BY-DAO)
      ; For safety check that the governor doesn't already exist
      (with-default-read governors-tab governor-name {'enabled:false}
                                                     {'enabled:= already-enabled}
        (enforce (not already-enabled) "Governor is already enabled"))

      ; Insert the governor
      (write governors-tab governor-name
             {'name: governor-name,
              'enabled: true,
              'guard: guard
             })
  ))

  (defun revoke-governor (governor-name:string)
    @doc "Revoke a governor => Need a vote"
    ; Revoking a governor is only allowed by a full DAO vote
    (with-capability (APPROVED-BY-DAO)
      ; For safety check that the governor  already exist
      (with-read governors-tab governor-name {'enabled:= enabled}
        (enforce enabled "Governor is already disabled"))

      (update governors-tab governor-name {'enabled: false})
  ))

  (defun list-governors ()
    (select governors-tab (where 'enabled (= true))))

  (defun proposal-key (id:integer)
     (int-to-str 10 id))


  (defun propose (description:string _hash:string transaction-data:string)
    (with-capability (PROPOSE description _hash)
    (enforce (= (hash transaction-data) _hash) "Hash does not match")
    (with-default-read proposal-id-tab  "LAST" {'id:0} {'id:=current-id}
      (let ((new-id (+ current-id 1)))
        (update proposal-id-tab "LAST" {'id:new-id})
        (insert proposal-id-tab _hash {'id:new-id})
        (insert proposal-tab (proposal-key new-id)
          { 'id:new-id,
            'description:description,
            'hash:_hash,
            'transaction-data: transaction-data,
            'end-time: (add-time (now) PROPOSAL-VOTING-TIME),
            'action-time: (add-time (now) PROPOSAL-ACTION-TIME),
            'validated: false,
            'yes:0.0,
            'no:0.0,
            'neutral: 0.0,
            'count:0
          })))
  ))

  (defun list-proposals-in-vote ()
    (select proposal-tab (where 'end-time (is-future)))
  )

  (defun list-proposals-archive ()
    (select proposal-tab (where 'action-time (is-past)))
  )

  (defun list-proposals-voted ()
    (select proposal-tab (and? (where 'end-time (is-future))
                               (where 'action-time (is-past))))
  )

  (defun gen-ballot-id (account:string proposal-id:integer)
    (hash {'a: account, 'i:proposal-id}))

  (defun vote (proposal-id:integer voting-account:string voting-amount:decimal _vote:string)
    ; Prevent double voting
    (let ((ballot-id (gen-ballot-id voting-account proposal-id)))
      (with-default-read voter-tab ballot-id {'voted:false} {'voted:= already-voted}
        (enforce (not already-voted) "This account has already voted for this proposal")
        (insert voter-tab ballot-id {'voted:true})))


    (let ((vote (upper _vote))
          (_proposal-id (proposal-key proposal-id)))
      ; Check that the vote is an allowed string
      (enforce (contains vote ["YES", "NO", "NEUTRAL"]) "Voting string invalid")
      (with-read proposal-tab _proposal-id
                 {'end-time:= end-time,
                  'yes:= yes,
                  'no:= no,
                  'neutral:= neutral,
                  'count:=cnt
                }
        ; Check that voting is possible
        (enforce (is-future end-time) "Voting period elapsed")

        ; Lock the governance token
        (free.dora.lock-until voting-account voting-amount (add-time end-time EXTRA-LOCKING-TIME))

        ; Store the vote
        (update proposal-tab _proposal-id
          {'yes:     (if (= vote "YES") (+ yes voting-amount) yes),
           'no:      (if (= vote "NO") (+ no voting-amount) no),
           'neutral: (if (= vote "NEUTRAL") (+ neutral voting-amount) neutral),
           'count:   (+ cnt 1)
          })))
  )

  (defun voting-details:object (proposal-id: integer)
    (read proposal-tab (int-to-str 10 proposal-id))
  )


  (defun get-voting-result:object ()
    ; First obtain the proposal-id
    (with-default-read proposal-id-tab (tx-hash) {'id:-1} {'id:=proposal-id}
      (enforce (!= -1 proposal-id) "Transaction was never proposed")

      ; Then get all the details of the proposal
      (with-read proposal-tab (proposal-key proposal-id)
        {
          'id:= _proposal-id,
          'hash:= _hash,
          'end-time:= end-time,
          'action-time:=action-time,
          'validated:= validated,
          'yes:= yes,
          'no:= no,
          'neutral:= neutral
        }
        ;; Sanity checks should never happen
        (enforce (= (tx-hash) _hash) "Hashes do not match")
        (enforce (= proposal-id _proposal-id) "Ids do not match")

        ;; Date checks
        (enforce (is-past end-time) "Approval too early => Vote is not finished")
        (enforce (is-future action-time) "Approval too late => Not possible to validate transaction")

        ;; Check states of the proposal
        (enforce (not validated) "The transaction has already been validated")

        ; Mark the transaction has being validated
        (update proposal-tab (proposal-key proposal-id) {'validated:true})

        ; Return the result in ratio
        (let ((total (sum3 yes no neutral)))
          (enforce (> total 0.0) "Nobody has voted")
          {'yes: (/ yes total),
           'no: (/ no  total),
           'neutral: (/ neutral total)})))
  )


  (defun approve-transaction-by-governor ()
    (enforce-guard-any (map (at 'guard) (select governors-tab ['guard] (where 'enabled (= true)))))
  )

  (defun list-guards ()
    (map (at 'guard) (select governors-tab ['guard] (where 'enabled (= true))))
  )

  (defun enforce-approve-transaction ()
    (if (= ""  (at 'sender (chain-data)))
        ; if the sender is empty: this can only be a local trx => Approve
        (concat ["Transaction approved:" (tx-hash) ])
        ; else use the DAO votes to enforce
        (bind (get-voting-result) {'yes:=yes, 'no:=no}
          ;; Vote checks
          (enforce (> yes no) "The approval hasn't been approved")

          ; Return a nice looking string
          (concat ["Transaction approved:" (tx-hash)])))
  )

  (defun init ()
    (insert proposal-id-tab "LAST" {'id:0})
  )
)
