import org.hyperledger.fabric.shim.ChaincodeBase;
import org.hyperledger.fabric.shim.ChaincodeStub;

class Ticket {
	byte[] owner;
	byte number;

        public Ticket(byte[] owner, byte number){
           this.owner = owner;
           this.number  = number;
        }

        public byte[] toBytes(){

           byte[] result = new byte[owner.length + 1];
           result[0] = number;
           for(int i = 0; i < owner.length; i++) {result[i+1] = owner[i];}
           return result;
        }

        public static Ticket readTicket(byte[] bytes){

           byte number = bytes[0];

           byte[] owner = new byte[bytes.length - 1];

           for(int i = 0; i < owner.length; i++) {owner[i] = bytes[i+1];}

           return new Ticket(owner, number);
        }
}

public class Lottery extends ChaincodeBase {




static final int price = 5;

static int ticketID = 0;
 

// @model int prize = ledger.size * price;

 

/*@
public normal_behaviour
ensures true;
@*/
Response addTicket(ChaincodeStub stub, byte[] owner, byte numbers) {

	Ticket ticket = new Ticket(owner, numbers);

	byte[] ticketAsBytes = ticket.toBytes();        

	stub.putState(ticketID, ticketAsBytes);
        ticketID++;

	return newSuccessResponse("Ok.");
}
/* @
public normal_behaviour
ensures (\forall int i; 0<=i && i < \result.length; \result[i].numbers == args[1]);
@*/
Response draw(ChaincodeStub stub, byte number) {
        Ticket[] winner = new Ticket[ticketID];
        int winnerCount = 0;
        for(int i = 0; i < ticketID; i++){             
            byte[] ticketAsBytes = stub.getState(i);
            Ticket t = Ticket.readTicket(ticketAsBytes);
            if(t == null){
               continue;
            }
            if(t.number == number){
               winner[i] = t;
               winnerCount++;
            }            
        }

	return newSuccessResponse("Winners: "+winnerCount);
}

}
