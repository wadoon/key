


public class Test extends ArrayList {

    
    public static void main(String[] args) {
        Test test = new Test();

        int totalExecutions = 10000;
        
        long startTime = System.currentTimeMillis();
        
        for (int i = 0; i < totalExecutions; i++) {
            test.execute();
        }
        

        long endTime = System.currentTimeMillis();
        long totalTime = endTime - startTime;

        System.out.print(totalTime);
        

    }



    public Test(){
        elementData = new SimpleObject[100000];
        
    }
    

    public int execute(){
        SimpleObject o = new SimpleObject();
        int start = 0;
        int end = elementData.length;
        int index = indexOfRange(o, start, end);
        return index;
    }
	
}

