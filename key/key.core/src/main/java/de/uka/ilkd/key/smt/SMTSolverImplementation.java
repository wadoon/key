// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.smt.processcomm.AbstractSolverSocket;
import de.uka.ilkd.key.smt.processcomm.ExternalProcessLauncher;
import de.uka.ilkd.key.smt.processcomm.SolverCommunication;
import de.uka.ilkd.key.smt.processcomm.SolverCommunication.Message;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.taclettranslation.assumptions.TacletSetTranslation;

final class SMTSolverImplementation implements SMTSolver, Runnable{
 
    private static AtomicInteger IDCounter = new AtomicInteger();

    private final int ID = IDCounter.incrementAndGet();
        
        private AbstractSolverSocket socket;
        
        private ModelExtractor query;

		/** The SMT problem that is related to this solver */
        private SMTProblem problem;

        /** It is possible that a solver has a listener. */
        private SolverListener listener;

        /** starts a external process and returns the result */
        private ExternalProcessLauncher<SolverCommunication> processLauncher;
   
        /**
         * The services object is stored in order to have the possibility to
         * access it in every method
         */
        private Services services;

        /**
         * The record of the communication between KeY and the given solver. If everything works fine,
         * it also contains the final result.
         */
    private final SolverCommunication solverCommunication = new SolverCommunication();
        
        /**
         * This holds information relevant for retrieving information on a model
         * from an SMT instance.
         * null in the beginning, is created at translation time.
         * FIXME: Why is this here? It is currently not being used!
         */
        // private ProblemTypeInformation problemTypeInformation = null;

        /** The thread that is associated with this solver. */
        private Thread thread;
        /**
         * The timeout that is associated with this solver. Represents the
         * timertask that is started when the solver is started.
         */
        private SolverTimeout solverTimeout;

        private ReasonOfInterruption reasonOfInterruption = ReasonOfInterruption.NoInterruption;
        private SolverState solverState = SolverState.Waiting;

        private final SolverType type;
        /** Strores the settings that are used for the execution. */
        private SMTSettings smtSettings;

        /**
         * Stores the translation of the problem that is associated with this
         * solver
         */
        private String problemString = "NOT YET COMPUTED";
        /** Stores the taclet translation that is associated with this solver. */
        private TacletSetTranslation tacletTranslation;
        /**
         * If there was an exception while executing the solver it is stored in
         * this attribute
         */
        private Throwable exception;
        
        private Collection<Throwable> exceptionsForTacletTranslation = new LinkedList<Throwable>();

        SMTSolverImplementation(SMTProblem problem, SolverListener listener,
                        Services services, SolverType myType) {
                this.problem = problem;
                this.listener = listener;
                this.services = services;
                this.type = myType;
                this.socket = AbstractSolverSocket.createSocket(type, query);
        processLauncher = new ExternalProcessLauncher<>(solverCommunication, type.getDelimiters());

        }

        /**
         * Starts a solver process. This method should be accessed only by an
         * instance of <code>SolverLauncher</code>. If you want to start a
         * solver please have a look at <code>SolverLauncher</code>.
         * 
         * @param timeout
         * @param settings
         */
    @Override
        public void start(SolverTimeout timeout, SMTSettings settings) {
                thread = new Thread(this,"SMTProcessor");
                solverTimeout = timeout;
                smtSettings = settings;
                thread.start();
        }

        @Override
        public ReasonOfInterruption getReasonOfInterruption() {
                return isRunning() ? ReasonOfInterruption.NoInterruption
                                : reasonOfInterruption;
        }

        public Throwable getException() {
                return isRunning() ? null : exception;
        }

        public SMTProblem getProblem() {
                return isRunning() ? null : problem;
        }

    public void setReasonOfInterruption(ReasonOfInterruption reasonOfInterruption) {
                        this.reasonOfInterruption = reasonOfInterruption;
        }

        private void setReasonOfInterruption(
                        ReasonOfInterruption reasonOfInterruption, Throwable exc) {
                        this.reasonOfInterruption = reasonOfInterruption;
                        this.exception = exc;
        }

        @Override
        public SolverType getType() {
                return type;
        }

        @Override
        public long getStartTime() {
                if (solverTimeout == null) {
                        return -1;
                }
                return solverTimeout.scheduledExecutionTime();
        }

        @Override
        public long getTimeout() {
                if (solverTimeout == null) {
                        return -1;
                }
                return solverTimeout.getTimeout();
        }

        @Override
        public SolverState getState() {
                        SolverState b = solverState;
                        return b;
        }

        private void setSolverState(SolverState value) {
                        solverState = value;
        }

        @Override
        public boolean wasInterrupted() {
                return getReasonOfInterruption() != ReasonOfInterruption.NoInterruption;
        }

        @Override
        public boolean isRunning() {
                return getState() == SolverState.Running;
        }


        @Override
        public void run() {
        		
                // Firstly: Set the state to running and inform the listener.
                setSolverState(SolverState.Running);
                listener.processStarted(this, problem);
                                
                // Secondly: Translate the given problem
                String commands[];
                try {
                        commands = translateToCommand(problem.getSequent());
                        // JS: debug start
                    String filename = "/tmp/SMTLIB-TL_" + problem.getName().replaceAll(" ", "");
                    System.out.println("SMTLIB translation has been written to file: " + filename);
                    BufferedWriter writer = new BufferedWriter(new FileWriter(filename));
                    writer.write(problemString);
                    writer.close();
                    // JS: debug end
                } catch (Throwable e) {
                    interruptionOccurred(e);
                    listener.processInterrupted(this, problem, e);
                    setSolverState(SolverState.Stopped);
                    solverTimeout.cancel();
                    return;
                }


            // Thirdly: start the external process.
            try {
                processLauncher.launch(commands);
                processLauncher.sendMessage(type.modifyProblem(problemString));

                //JS: Debug start
                String filename = "/tmp/SolverOutput_" + socket.getName() + "_" + problem.getName().replaceAll(" ", "");
                BufferedWriter writer = new BufferedWriter(new FileWriter(filename));
                writer.write(socket.getName() + " says: \n");
                Message msg = processLauncher.getPipe().readMessage();
                //JS: Debug end
                while (msg != null) {
                    writer.append(msg.getContent() + "\n");
                    socket.messageIncoming(processLauncher.getPipe(), msg);
                    msg = processLauncher.readMessage();
                }
                //JS: Debug start
                writer.close();
                System.out.println("Solver answer has been written to file: " + filename);
                //JS: Debug end

                // uncomment for testing
                //  Thread.sleep(3000);
                // uncomment for testing
                // Random random = new Random();
                //Thread.sleep(random.nextInt(3000)+1000);
                //throw new RuntimeException("Test exception");
            } catch (Throwable e) {
                interruptionOccurred(e);
            } finally {
                // Close everything.
                // System.out.println(name() + " : " + solverCommunication.getFinalResult());

                solverTimeout.cancel();
                setSolverState(SolverState.Stopped);
                listener.processStopped(this, problem);
                processLauncher.stop();
            }

        }

        private void interruptionOccurred(Throwable e) {
                ReasonOfInterruption reason = getReasonOfInterruption();
                switch (reason) {
                case Exception:
                case NoInterruption:
                setReasonOfInterruption(ReasonOfInterruption.Exception, e);
                        listener.processInterrupted(this, problem, e);
                        break;
                case Timeout:
                        listener.processTimeout(this, problem);
                        break;
                case User:
                        listener.processUser(this, problem);
                        break;
                }
        }

        @Override
        public String name() {
                return type.getName();
        }

        private static String indent(String string) {
            try {
                return SMTBeautifier.indent(string);
            } catch (Exception ex) {
                // fall back if pretty printing fails
                ex.printStackTrace();
                return string;
            }
        }


    private String[] translateToCommand(Sequent sequent)
                throws IllegalFormulaException, IOException {
        if (getType() == SolverType.Z3_CE_SOLVER) {
            Proof proof = problem.getGoal().proof();
            SpecificationRepository specrep = proof.getServices().getSpecificationRepository();

            Proof originalProof = null;
            for (Proof pr : specrep.getAllProofs()) {
                if (proof.name().toString().endsWith(pr.name().toString())) {
                    originalProof = pr;
                    break;
                }
            }
            // System.out.println(originalProof.name());

            KeYJavaType typeOfClassUnderTest =
                    specrep.getProofOblInput(originalProof).getContainerType();

            SMTObjTranslator objTrans =
                    new SMTObjTranslator(smtSettings, services, typeOfClassUnderTest);
            problemString = objTrans.translateProblem(sequent, services, smtSettings).toString();
            // problemTypeInformation = objTrans.getTypes();
            ModelExtractor query = objTrans.getQuery();
            getSocket().setQuery(query);
            tacletTranslation = null;

        } else {
            SMTTranslator trans = getType().createTranslator(services);
            //instantiateTaclets(trans);
            problemString = indent(trans.translateProblem(sequent, services, smtSettings).toString());
//            tacletTranslation = ((AbstractSMTTranslator) trans).getTacletSetTranslation();
            if(trans instanceof AbstractSMTTranslator) {
                // Since taclet translation in the old form is no longer used,
                // this will likely disappear.
                exceptionsForTacletTranslation.addAll(
                        ((AbstractSMTTranslator) trans).getExceptionsOfTacletTranslation());
            }
        }

        String parameters [] = this.type.getSolverParameters().split(" ");
        String result [] = new String[parameters.length + 1];
        for (int i = 0; i < result.length; i++) {
            result[i] = i == 0 ? type.getSolverCommand() : parameters[i - 1];
        }
        return result;
    }

        @Override
        public void interrupt(ReasonOfInterruption reason) {

                // order of assignments is important;
                setReasonOfInterruption(reason);
                setSolverState(SolverState.Stopped);
                if (solverTimeout != null) {
                        solverTimeout.cancel();
                }
                if (thread != null) {
                		processLauncher.stop();
                        thread.interrupt();
                }

        }

        @Override
        public SMTSolverResult getFinalResult() {

                return isRunning() ? null : solverCommunication.getFinalResult();
        }

        @Override
        public TacletSetTranslation getTacletTranslation() {
                return isRunning() ? null : tacletTranslation;
        }

        @Override
        public String getTranslation() {
                return isRunning() ? null : problemString;
        }

        @Override
        public String toString() {
                return name() + " (ID: " + ID + ")";
        }

        @Override
        public String getSolverOutput() {       	
        	
         		String output = "";
        		output+= "Result: "+ solverCommunication.getFinalResult().toString()+"\n\n";
        		
        		for(String s : solverCommunication.getMessages()){
        			
        			if(s.equals("endmodel")){
        				break;
        			}
        			
        			output += s+"\n";	
        			
        		}
        		
        		if(getSocket().getQuery()!=null){
        			ModelExtractor mq = getSocket().getQuery();
        			Model m = mq.getModel();
        			if(m!=null){
        				output += "\n\n";
        				output += m.toString();
        			}
        			
        			
        			
        		}		
        		
                return output;
        }

        @Override
        public Collection<Throwable> getExceptionsOfTacletTranslation() {
                return exceptionsForTacletTranslation;
        }

		@Override
        public AbstractSolverSocket getSocket() {
	        return socket;
        }

    public ModelExtractor getQuery() {
        return query;
    }

    public void setQuery(ModelExtractor query) {
        this.query = query;
    }

}
