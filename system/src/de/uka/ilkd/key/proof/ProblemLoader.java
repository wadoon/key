// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.StringReader;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstDirect;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.init.ABSProblemInitializer;
import de.uka.ilkd.keyabs.init.ABSProfile;
import de.uka.ilkd.keyabs.po.ABSKeYUserProblemFile;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}.
 * It allows to do the loading process as {@link SwingWorker} {@link Thread}
 * and it opens the proof obligation browser it is not possible to instantiate
 * a proof configured by the opened file.
 * @author Martin Hentschel
 */
public final class ProblemLoader extends DefaultProblemLoader implements Runnable {
    private SwingWorker worker;
    private ProverTaskListener ptl;
    
    public ProblemLoader(File file, List<File> classPath, File bootClassPath, KeYMediator mediator) {
        super(file, classPath, bootClassPath, mediator);
    }

    public void addTaskListener(ProverTaskListener ptl) {
        this.ptl = ptl;
    }
    

    public void run() {
        /* Invoking start() on the SwingWorker causes a new Thread
         * to be created that will call construct(), and then
         * finished().  Note that finished() is called even if
         * the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        worker = new SwingWorker() {
                private long time;
		public Object construct() {
                    time = System.currentTimeMillis();
                    String res = doWork();
                    time = System.currentTimeMillis() - time;
		    return res;
		}
		public void finished() {
		   getMediator().startInterface(true);
		    final String msg = (String) get();
		    if (ptl != null) {                        
                        final TaskFinishedInfo tfi = new DefaultTaskFinishedInfo(ProblemLoader.this, 
                                msg, getProof(), time, 
                                (getProof() != null ? getProof().countNodes() : 0),                                
                                (getProof() != null ? getProof().countBranches() -
                                      getProof().openGoals().size() : 0));
                        ptl.taskFinished(tfi);
		    }
		}
        };
        getMediator().stopInterface(true);
        if (ptl != null) { 
        	ptl.taskStarted("Loading problem ...", 0);
        }
        worker.start();
    }
    
    
    
   private String doWork() {
      String status = "";
      ProofOblInput po = null;
      try {
         try {
            status = load();
         }
         catch (ExceptionHandlerException e) {
            // e.printStackTrace();
            throw e;
         }
         catch (Throwable thr) {
            getExceptionHandler().reportException(thr);
            status = thr.getMessage();
            System.err.println("2");
         }
      }
      catch (ExceptionHandlerException ex) {
         String errorMessage = "Failed to load " + (getEnvInput() == null ? "problem/proof" : getEnvInput().name());
         getMediator().getUI().notify(new ExceptionFailureEvent(errorMessage, ex));
         getMediator().getUI().reportStatus(this, errorMessage);
         status = ex.toString();
      }
      finally {
         getMediator().resetNrGoalsClosedByHeuristics();
         if (po instanceof KeYUserProblemFile) {
            ((KeYUserProblemFile) po).close();
         }
      }
      return status;
   }

   public KeYExceptionHandler getExceptionHandler() {
       return getMediator().getExceptionHandler();
   }
   
   @Override
   protected String selectProofObligation() {
      ProofManagementDialog.showInstance(getMediator(), getInitConfig());
      if (ProofManagementDialog.startedProof()) {
         return "";
      }
      else {
         return "Aborted.";
      }
   }
}
