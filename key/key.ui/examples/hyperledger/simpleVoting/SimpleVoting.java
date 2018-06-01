import javax.json.Json;

import org.hyperledger.fabric.shim.ChaincodeBase;
import org.hyperledger.fabric.shim.ChaincodeStub;


public class SimpleVoting extends ChaincodeBase {

    /*@ private behaviour
      @
      @*/
    private static /*@ pure @*/ String toString(byte[] bs, int start, int end) {
        if (start < 0 || start > end || bs.length <= end) {
            throw new IllegalArgumentException("Not a valid array segment.");
        }
        String res = "";
        for (int i = start; i <= end; i++) {
            res += new String(new byte[] {bs[i]});
        }
        return res;
    }

    /*@ private behaviour
      @
      @*/
    private static /*@ pure @*/ byte[] toBytes(SimpleElection elec) {
        byte[] id = elec.id.getBytes();
        byte[] votes = new byte[elec.votes.size() * 9];
        int keyNr = 0;
        for (String s: elec.votes.keySet()) {
            for (int i = 0; i < 8; i++) {
                votes[keyNr * 9 + i] = (byte) s.charAt(j);
            }
            votes[keyNr * 9 + 8] = (byte) elec.votes.get(s);
            keyNr++;
        }
        byte[] res = new byte[id.length + votes.length];
        for (int i = 0; i < id.length; i++) {
            res[i] = id[i];
        }
        for (int i = id.length; i < id.length + votes.length; i++) {
            res[i] = votes[i - id.length];
        }
        return res;
    }

    public final class SimpleElection {
        String id;
        Map<String, Vote> votes;

        /*@ private behaviour
          @ ensures (\forall int i; i % 9 == 0 ==> \result.get(toString(vs, i, i + 7)).decision == toString(vs, i + 8, i + 8));
          @*/
        private static /*@ pure @*/ Map<String, Vote> toVotes(byte[] vs) {
            Map<String, Vote> v = new LinkedHashMap<String, Vote>();
            for (int i = 0; i < vs.length; i += 9) {
                v.put(toString(vs, i, i + 7), new Vote(toString(vs, i + 8, i + 8)));
            }
            return v;
        }

        private SimpleElection() {}

        /*@ public behaviour
          @
          @*/
        public SimpleElection(String ident, byte[] vs) {
            id = ident;
            if (election.length % 9 != 0) {
                throw new IllegalArgumentException("The election contains invalid votes.");
            }
            votes = toVotes(vs);
        }

        /*@ public behaviour
          @ requires  9 <= elec.length;
          @ ensures id == toString(election, 0, 7);
          @ ensures (\forall int i; 0 <= i && i < elec.length - 8; );
          @*/
        public SimpleElection(byte[] elec) {
            if (elec.length < 9) {
                throw new IllegalArgumentException("Not a valid election.");
            }
            byte[] vs = new byte[elec.length - 8];
            for (int i = 0; i < vs.length; i++) {
                vs[i] = elec[i + 8];
            }
            SimpleElection(toString(election, 0, 7), vs);
        }
    }

    public final class Vote {
        String decision;

        private Vote() {}

        /*@ public behaviour
          @ ensures decision == d;
          @*/
        public Vote(String d) {
            decision = d;
        }
    }

    /*@ private behaviour
      @
      @*/
    private SimpleElection getState(ChaincodeStub stub, String s) {
        final byte[] election = stub.getState(s);
        if (election.length < 9) {
            throw new IllegalArgumentException("Not a valid election.");
        }
        return new SimpleElection(election);
    }

    /*@ private behaviour
      @
      @*/
    private SimpleElection putState(ChaincodeStub stub, SimpleElection e) {
        stub.putState(e.id, toBytes(e));
    }

    /*@ private behaviour
      @
      @*/
    private Response putVote(ChaincodeStub stub, SimpleElection elec, String vid, Vote v) {
        if (elec.votes.containsKey(voterID)) {
            throw new IllegalArgumentException("You already voted.");
        }
        elec.votes.put(vid, v);
        putState(stub, elec);
        return newSuccessResponse("Successfully inserted vote " + vid + " with value "+ v.decision +" into election "+ elec.id +".");
    }

    /*@ private behaviour
      @
      @*/
    private Response getVote(ChaincodeStub stub, SimpleElection elec, String voterID) {
        if (!elec.votes.containsKey(voterID)) {
            throw new IllegalArgumentException("You did not vote.");
        }
        return newSuccessResponse(Json.createObjectBuilder()
                                    .add("Election", elec.id)
                                    .add("Voter", voterID)
                                    .add("Decision", elec.votes.get(voterID))
                                    .build().toString().getBytes());
    }

    /*@ private behaviour
      @
      @*/
    private Response computeResult(SimpleElection elec) {
        int numberYes = 0;
        int numberNo = 0;
        for (VoterID vid : elec.votes.keySet()) {
            Vote v = elec.votes.get(vid);
            if (v.decision == "Yes") {
                numberYes++;
            } else if (v.decision == "No") {
                numberNo++;
            }
        }
        if (numberNo < numberYes) {
            return newSuccessResponse(Json.createObjectBuilder()
                                        .add("Election", elec.id)
                                        .add("Decision", "Yes")
                                        .build().toString().getBytes());
        }
        if (numberYes < numberNo) {
            return newSuccessResponse(Json.createObjectBuilder()
                                        .add("Election", elec.id)
                                        .add("Decision", "No")
                                        .build().toString().getBytes());
        }
        return newSuccessResponse("No election result for election " + elec.id + ".");
    }

    /*@ private behaviour
      @
      @*/
    private Response castVote(ChaincodeStub stub, String[] args) {
        if (args.length != 3) {
            throw new IllegalArgumentException("Incorrect number of arguments. Expecting 3");
        }
        final String electionID = args[0];
        final String voterID = args[1];
        final String vote = args[2];

        final SimpleElection election = getState(stub, electionID);
        if (election == null) {
            throw new IllegalArgumentException("Invalid election.");
        }

        Response r = putVote(stub, election, voterID, vote);
        if (r != null) {
            return r;
        } else {
            return newSuccessResponse("OK.");
        }
    }

    /*@ private behaviour
      @
      @*/
    private Response checkVote(ChaincodeStub stub, String[] args) {
        if (args.length != 2) {
            throw new IllegalArgumentException("Incorrect number of arguments. Expecting 3");
        }
        String electionID = args[0];
        String voterID = args[1];
        
        final SimpleElection election = getState(stub, electionID);
        if (election == null) {
            throw new IllegalArgumentException("Election does not exist.");
        }
        
        return getVote(stub, election, voterID);
    }

    /*@ private behaviour
      @
      @*/
    private Response createElection(ChaincodeStub stub, String[] args) {
        if (args.length != 1) {
            throw new IllegalArgumentException("Incorrect number of arguments. Expecting 1");
        }
        String electionID = args[0];

        final SimpleElection elec = new SimpleElection(electionID, new byte[0]);
        putState(stub, elec);
        return newSuccessResponse("OK.");
    }

    /*@ private behaviour
      @
      @*/
    private Response closeElection(ChaincodeStub stub, String[] args) {
        if (args.length != 1) {
            throw new IllegalArgumentException("Incorrect number of arguments. Expecting 1");
        }
        String electionID = args[0];
        
        final SimpleElection election = getState(stub, electionID);
        if (election == null) {
            throw new IllegalArgumentException("Election does not exist.");
        }
        return computeResult(election);
    }

    /*@ private behaviour
      @
      @*/
    private Response voterNumber(ChaincodeStub stub, String[] args) {
        if (args.length != 1) {
            throw new IllegalArgumentException("Incorrect number of arguments. Expecting 1");
        }
        String electionID = args[0];
        final SimpleElection election = getState(stub, electionID);
        if (election == null) {
            throw new IllegalArgumentException("Election does not exist.");
        }
        return newSuccessResponse(Json.createObjectBuilder()
                                    .add("Election", election.id)
                                    .add("Size", election.votes.size())
                                    .build().toString().getBytes());
    }

//     @Override
//     public Response invoke(ChaincodeStub stub) {
//         try {
//             final String function = stub.getFunction();
//             final String[] args = stub.getParameters().stream().toArray(String[]::new);
//             
//             switch (function) {
//                 case "castVote":
//                     return play(stub, args);
//                 case "createElection":
//                     return createGame(stub, args);
//                 case "closeElection":
//                     return createGame(stub, args);
//                 case "checkVote":
//                     return checkVote(stub, args);
//                 case "voterNumber":
//                     return voterNumber(stub, args);
//                 default:
//                     return newErrorResponse("Unknown function: " + function);
//             }
//         } catch (Throwable e) {
//             return newErrorResponse(e);
//         }
//     }

//     @Override
//     public Response init(ChaincodeStub stub) {
//         final String function = stub.getFunction();
//         if (!function.equals("init")) {
//             return newErrorResponse("Unknown function: " + function);
//         }
//         return init(stub, stub.getParameters().stream().toArray(String[]::new));
//     }

//     public static void main(String[] args) throws Exception {
//         new SimpleVoting().start(args);
//     }
}
