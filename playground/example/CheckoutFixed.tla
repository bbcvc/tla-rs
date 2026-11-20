---- MODULE CheckoutFixed ----
\* A checkout whose payment can time out. When the bank captures the money it queues a callback,
\* which reaches the shop later and marks the order paid. A job refunds money captured for a
\* cancelled order. The callback handler leaves a cancelled order cancelled, and the refund job
\* gives its money back.

VARIABLES order, payment, callback
vars == <<order, payment, callback>>

TypeOK ==
    /\ order \in {"cart", "awaiting payment", "paid", "shipped", "cancelled"}
    /\ payment \in {"none", "pending", "captured", "refunded"}
    /\ callback \in {"none", "in flight"}

Init == order = "cart" /\ payment = "none" /\ callback = "none"

YouPlaceTheOrder ==
    /\ order = "cart"
    /\ order' = "awaiting payment" /\ payment' = "pending" /\ UNCHANGED callback

TheBankCaptures ==
    /\ payment = "pending"
    /\ payment' = "captured" /\ callback' = "in flight" /\ UNCHANGED order

\* The fix: only an order still awaiting payment becomes paid.
TheCallbackArrives ==
    /\ callback = "in flight"
    /\ callback' = "none"
    /\ order' = IF order = "awaiting payment" THEN "paid" ELSE order
    /\ UNCHANGED payment

ThePaymentTimesOut ==
    /\ order = "awaiting payment"
    /\ order' = "cancelled" /\ UNCHANGED <<payment, callback>>

TheRefundJobRuns ==
    /\ order = "cancelled" /\ payment = "captured"
    /\ payment' = "refunded" /\ UNCHANGED <<order, callback>>

TheWarehouseShips ==
    /\ order = "paid"
    /\ order' = "shipped" /\ UNCHANGED <<payment, callback>>

Done == order \in {"shipped", "cancelled"} /\ callback = "none" /\ UNCHANGED vars

Next ==
    \/ YouPlaceTheOrder \/ TheBankCaptures \/ TheCallbackArrives \/ ThePaymentTimesOut
    \/ TheRefundJobRuns \/ TheWarehouseShips \/ Done

Spec == Init /\ [][Next]_vars

\* We never ship an order whose money we gave back.
NeverShipRefunded == ~(order = "shipped" /\ payment = "refunded")
====
