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
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.KeYExceptionHandler;

/**
 * This class extends the functionality of the {@link DefaultProblemLoader}.
 * It allows to do the loading process as {@link SwingWorker} {@link Thread}
 * and it opens the proof obligation browser it is not possible to instantiate
 * a proof configured by the opened file.
 * @author Martin Hentschel
 */
public final class ProblemLoader<S extends IServices, IC extends InitConfig<S, IC>> implements Runnable {
    
    
    private final DefaultProblemLoader<S, IC> loader;
    
    public int hashCode() {
        return loader.hashCode();
    }

    public String load() throws ProofInputException, IOException {
        return loader.load();
    }

    public boolean equals(Object obj) {
        return loader.equals(obj);
    }

    public String toString() {
        return loader.toString();
    }

    public File getFile() {
        return loader.getFile();
    }

    public List<File> getClassPath() {
        return loader.getClassPath();
    }

    public File getBootClassPath() {
        return loader.getBootClassPath();
    }

    public KeYMediator<S, IC> getMediator() {
        return loader.getMediator();
    }

    public EnvInput<S, IC> getEnvInput() {
        return loader.getEnvInput();
    }

    public AbstractProblemInitializer<S, IC> getProblemInitializer() {
        return loader.getProblemInitializer();
    }

    public IC getInitConfig() {
        return loader.getInitConfig();
    }

    public Proof getProof() {
        return loader.getProof();
    }

    private SwingWorker worker;
    private ProverTaskListener ptl;
    
    
    
    public ProblemLoader(DefaultProblemLoader<S, IC> loader) {
        //super(file, classPath, bootClassPath, mediator);
        this.loader = loader;
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
