export const title = "Checkout with a payment timeout";
export const state = (v) => ({
  Order: { cart: "Cart", "awaiting payment": "Awaiting payment", paid: "Paid", shipped: "Shipped", cancelled: "Cancelled" }[v.order],
  Money: { none: "Not charged", pending: "Charge pending", captured: "Charged", refunded: "Refunded" }[v.payment],
});
const words = {
  YouPlaceTheOrder: "you place the order",
  TheBankCaptures: "the bank takes the money",
  TheCallbackArrives: "the bank's callback arrives",
  ThePaymentTimesOut: "the payment times out",
  TheRefundJobRuns: "the refund job gives the money back",
  TheWarehouseShips: "the warehouse ships",
  Done: null,
};
export const step = (action) => words[action];
