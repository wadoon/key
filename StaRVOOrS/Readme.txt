		*****************************
		*         StaRVOOrS         *
		*****************************

This folder contains all content of the StaRVOOrS component to perform and analyze proofs.

Fore more details about this project visit 
http://www.cse.chalmers.se/~chimento/starvoors/
or contact Jesus Mauricio Chimento (chimento@chalmers.se).


(1) Project Description
-----------------------
The overall purpose of the StaRVOOrS project (`Unified Static and Runtime Verification of Object-Oriented Software') is to provide a unified, lightweight to use but powerful in result, method for specifying and verifying, with a variety of confidence levels, properties of parallel object-oriented software systems. 


(2) Repository File Structure
-----------------------------
The project folder is structured as follows:
- doc          // Additional documentation
- src          // Contains the whole source code
  - java
    - components // The full program logic as pure Java application
    - tests      // JUnit Tests for components (pure Java)
  - eclipse
    - features   // Contains the specified Eclipse features
    - plugins    // Provides the components as Eclipse plug-ins and an executable Eclipse product.
    - tests      // Provides the tests as Eclipse plug-ins
- Readme.txt:  // This file


(3) Setup Development IDE
-------------------------
Follow the steps in the sub sections precisely. Notice that you have to use
the mentioned Eclipse version!


(3.1) Setup KeY
---------------
Follow the instructions of Section (2) in '../key/Readme.txt' carefully


(3.2) Import Java Projects from GIT Repository
-------------------------------------------------
1. Select main menu item 'File, Import...'
2. Select 'General, Existing Projects into Workspace' and press 'Next >'
3. Set root directory to '<root>/GIT/KeY/StaRVOOrS/src/java'
4. Ensure that 'Copy projects into workspace' is NOT selected.
5. Finish the wizard


(4) Execute StaRVOOrS as Java Application
--------------------------------------------------------------
1. Open class 'org.key_project.starvoors.CasesGeneratorMain'
2. Click on context menu item 'Run As, Java Application'
   (From now on the created launch configuration can be used)


(5) Run JUnit Tests
-------------------
1. Open class 'org.key_project.sed.core.all.test.suite.AllSEDTests'
2. Select main menu item 'Run, Run As, JUnit Plug-in Test'
   (Terminate the launched JUnit Plug-in Test.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea


(6) Run SWTBot Tests
--------------------
1. Open class 'org.key_project.starvoors.test.suite.AllStaRVOOrSTests'
2. Select main menu item 'Run, Run As, JUnit Test'
   (Terminate the launched JUnit Test'.)
3. Select main menu item 'Run, Run Configurations...'
4. Select tab 'Arguments' and add the following 'VM arguments':
   -Xmx2048m -XX:MaxPermSize=256m -ea


(7) Deploy StaRVOOrS as pure Java application
---------------------------------------------
1. Run ant task 'deployAll' of '<root>/GIT/KeY/key/scripts/build.xml'
2. The result is stored at '<root>/GIT/KeY/key/deployment'
3. StaRVOOrS can be executed as follows:
   java -jar <root>/GIT/KeY/key/deployment/components/key.starvoors.jar
