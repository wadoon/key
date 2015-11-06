/**
 * 
 */
package application;


import javafx.event.ActionEvent;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuBar;
import javafx.scene.control.MenuItem;

/**
 * @author Maximilian
 *
 */
public class mainMenuBar extends MenuBar {
	final String[] mainMenu = new String[] {
			"Open",
			"Save",
			"Close"
	};
	

	/**
	 * 
	 */
	public mainMenuBar() {
		// TODO Auto-generated constructor stub
		super();
		
		Menu menuFile = new Menu("File");
		MenuItem open = new MenuItem("Open");
		open.setOnAction((ActionEvent e) ->{
			System.out.println("Open a File");
		});
		MenuItem save = new MenuItem("Save");
		save.setOnAction((ActionEvent e) ->{
			System.out.println("Save a File");
		});
		MenuItem close = new MenuItem("Close");
		close.setOnAction((ActionEvent e) ->{
			System.exit(0);
		});
		menuFile.getItems().addAll(open, save, close);
		
		Menu menuEdit = new Menu("Edit");
		
		this.getMenus().addAll(menuFile, menuEdit);
	}

	/**
	 * @param arg0
	 */
	public mainMenuBar(Menu... arg0) {
		super(arg0);
		// TODO Auto-generated constructor stub
	}

}
