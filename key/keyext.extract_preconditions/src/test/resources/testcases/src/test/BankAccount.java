class BankAccount {
    private /*@ spec_public @*/ int balance;

    public BankAccount() {
        this.balance = 0;
    }

    /*@ public normal_behavior
      @ requires amount>0 && balance > 0;
      @ ensures balance>0;
     */
    // Kontoführungsgebühren! werden übersehen
    public boolean withdraw(int amount) {
        if (balance < amount - 5) {
            return false;
        } else {
            balance -= amount;
            return true;
        }
    }
}