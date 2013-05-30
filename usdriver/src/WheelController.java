package warwick.marsh.ultracam.usdriver;

import java.lang.Void;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.SwingWorker;

import java.awt.*;              //for layout managers and more
import java.awt.event.*;        //for action events

import java.net.*;
import java.io.*;

public class WheelController extends JFrame 
    implements ActionListener, WindowListener {

    private static final int WIDTH  = 300;
    private static final int HEIGHT = 200;
    
    // Colours and Fonts
    public static final Color DEFAULT_COLOUR    = new Color(220, 220, 255);
    public static final Color SEPARATOR_BACK    = new Color(100, 100, 100);
    public static final Color SEPARATOR_FORE    = new Color(150, 150, 200);
    public static final Color LOG_COLOUR        = new Color(240, 230, 255);
    public static final Color ERROR_COLOUR      = new Color(255, 0,   0  );
    public static final Color WARNING_COLOUR    = new Color(255, 100, 0  );
    public static final Color GO_COLOUR         = new Color(0,   255, 0  );
    public static final Color STOP_COLOUR       = new Color(255, 0,   0  );
    public static final Font DEFAULT_FONT       = new Font("Dialog", Font.BOLD, 12);
    
    private FilterWheel wheel = null;
    
    private String[] names = null;
    
    //buttons and labels
    private JLabel currFiltLab;
    private JButton closeB, goB, homeB, initB;
    private JTextField currFilt;
    private JComboBox filtList;
    private Container pane;
    private JPanel blank;
    
    // constructor, layout elements and make visible
    public WheelController(String[] filtNames, FilterWheel aWheel){

	wheel = aWheel;
	names = filtNames;
	setLookFeel();
	
    	// set window title and create a pane to display things in
	setTitle("USPEC Filter Wheel Control");
    	pane = getContentPane();
    	pane.setLayout(new GridLayout(4,2));
	
	// try and connect to the wheel
    	try{
	    if(!wheel.isConnected()){
		wheel.connect();
		wheel.init();
	    }
	}catch(Exception e){
	    JOptionPane.showMessageDialog(pane,e.toString(),
					  "Filter Wheel Error",
					  JOptionPane.ERROR_MESSAGE);
	}    
	addWindowListener(this);
    	initComponents();
    	setCurrFilter();    
    	setVisible(true);    	
    	setResizable(false);
    }

    public void enableAll(){
    	Component[] comList = pane.getComponents();
    	for(Component thing : comList){
	    thing.setEnabled(true);
    	}
    }
    public void disableAll(){
        Component[] comList = pane.getComponents();
    	for(Component thing : comList){
	    thing.setEnabled(false);
    	}
    }

    public void refreshFiltChoice(){
    	filtList.removeAllItems();
    	for( String filt : names) {
	    filtList.addItem(filt);
    	}
    }
    
    public void setCurrFilter(){
    	SwingWorker<Integer,Void> worker = new SwingWorker<Integer,Void>(){
	    @Override
	    protected Integer doInBackground() throws Exception{
		int currPos = wheel.getPos();
		return currPos;
	    }
	    @Override
	    protected void done(){
		try{
		    int currPos = get(); // will throw err if one occurred on bgkrd thread
		    String thisFilt = names[currPos-1];
		    currFilt.setText(thisFilt);
		    filtList.setSelectedItem(thisFilt);
		}catch(Exception e){
		    JOptionPane.showMessageDialog(pane,
						  e.toString(),
						  "Filter Wheel Error",
						  JOptionPane.ERROR_MESSAGE);
		}
	    }
	};
	worker.execute();
    }
        
    public void initComponents(){
    
    	//label for current filter
    	currFiltLab = new JLabel("Current Filter: ",SwingConstants.RIGHT);
    	// textfield to hold it
    	currFilt = new JTextField(5);
    	currFilt.setEditable(false);
    	
    	// blank for spacing
    	blank = new JPanel();
    	
    	//buttons
    	closeB = new JButton("close");
    	closeB.setActionCommand("close");
    	closeB.addActionListener(this);	
    	goB    = new JButton("go");
    	goB.setActionCommand("go");
    	goB.addActionListener(this);
    	homeB    = new JButton("home");
    	homeB.setActionCommand("home");
    	homeB.addActionListener(this);
    	initB    = new JButton("init");
    	initB.setActionCommand("init");
    	initB.addActionListener(this);
    
	//filter chooser
	filtList = new JComboBox(names);
	filtList.addActionListener(this);
	filtList.setActionCommand("sel");
    	
    	// add things in the order you want them to appear (left to right, top to bottom)
    	pane.add(currFiltLab);
    	pane.add(currFilt);
    	pane.add(filtList); pane.add(goB); 
    	pane.add(homeB); pane.add(initB); 
    	pane.add(blank); pane.add(closeB);
    	
    	setSize(WIDTH,HEIGHT);
	// if the user clicks the x in top-right, let the program handle it
    	setDefaultCloseOperation(DO_NOTHING_ON_CLOSE);
    }

    public void actionPerformed(ActionEvent e){
	if(e.getActionCommand().equals("close")){
	    disableAll();
	    SwingWorker<Void,Void> worker = new SwingWorker<Void,Void>(){
		@Override
		protected Void doInBackground() throws Exception{
		    wheel.close();
		    return null;
		}
		@Override
		protected void done(){
		    enableAll();
		    try{
			get(); // will throw error if one occurred in background thread
			// this only gets done if no errors were thrown
			//System.exit(0);
			setVisible(false);
		    }catch(Exception e){
			JOptionPane.showMessageDialog(pane,
						      e.toString(),
						      "Filter Wheel Error",
						      JOptionPane.ERROR_MESSAGE);
			//System.exit(0);
			setVisible(false);
		    }
		}
	    };
	    worker.execute();
	}
	if(e.getActionCommand().equals("sel")){
	    goB.setBackground(GO_COLOUR);
	}
	if(e.getActionCommand().equals("home")){
	    //set home button to warning, to indicate something is changing
	    homeB.setBackground(WARNING_COLOUR);
	    disableAll();
	    //fire off home command on new thread
	    SwingWorker<Void,Void> worker = new SwingWorker<Void,Void>(){
		@Override
		protected Void doInBackground() throws Exception{
		    wheel.home();					
		    return null;
		}
		@Override
		protected void done(){
		    try{
			enableAll();
			get(); // will throw error if one occurred in background thread
			// this only gets done if no errors were thrown
			setCurrFilter();
			homeB.setBackground(DEFAULT_COLOUR);
			//JOptionPane.showMessageDialog(pane,"done");
		    }catch(Exception e){
			JOptionPane.showMessageDialog(pane,
						      e.toString(),
						      "Filter Wheel Error",
						      JOptionPane.ERROR_MESSAGE);
		    }
		}
	    };
	    worker.execute();		
	}
		
	if(e.getActionCommand().equals("init")){
	    disableAll();
	    initB.setBackground(WARNING_COLOUR);
	    //fire off init command on new thread
	    SwingWorker<Void,Void> worker = new SwingWorker<Void,Void>(){
		@Override
		protected Void doInBackground() throws Exception{
		    wheel.reSpawn();					
		    return null;
		}
		@Override
		protected void done(){
		    try{
			enableAll();
			get(); // will throw error if one occurred in background thread
			// this only gets done if no errors were thrown
			setCurrFilter();
			initB.setBackground(DEFAULT_COLOUR);
			//JOptionPane.showMessageDialog(pane,"done");
		    }catch(Exception e){
			JOptionPane.showMessageDialog(pane,
						      e.toString(),
						      "Filter Wheel Error",
						      JOptionPane.ERROR_MESSAGE);
		    }
		}
	    };
	    worker.execute();		
	}
		
	if(e.getActionCommand().equals("go")){
	    disableAll();
	    goB.setBackground(WARNING_COLOUR);
	    //fire off init command on new thread
	    SwingWorker<Void,Void> worker = new SwingWorker<Void,Void>(){
		@Override
		protected Void doInBackground() throws Exception{
		    int desiredPos = filtList.getSelectedIndex()+1;
		    wheel.move(desiredPos);			
		    return null;
		}
		@Override
		protected void done(){
		    try{
			enableAll();
			get(); // will throw error if one occurred in background thread
			// this only gets done if no errors were thrown
			goB.setBackground(DEFAULT_COLOUR);
			setCurrFilter();
			//JOptionPane.showMessageDialog(pane,"done");
		    }catch(Exception e){
			JOptionPane.showMessageDialog(pane,
						      e.toString(),
						      "Filter Wheel Error",
						      JOptionPane.ERROR_MESSAGE);
		    }
		}
	    };
	    worker.execute();		
	}
		
    }

    //---------------------------------
    // Window Events
    //---------------------------------
    public void windowClosing(WindowEvent e) {
	// handle clicks on close 'cross' elegantly
	closeB.doClick();
    }
    public void windowClosed(WindowEvent arg0) {
	//System.out.println("Window close event occur");
    }
    public void windowActivated(WindowEvent arg0) {
	//System.out.println("Window Activated");
    }
    public void windowDeactivated(WindowEvent arg0) {
	//System.out.println("Window Deactivated");
    }
    public void windowDeiconified(WindowEvent arg0) {
	//System.out.println("Window Deiconified");
    }
    public void windowIconified(WindowEvent arg0) {
	//System.out.println("Window Iconified");
    }
    public void windowOpened(WindowEvent arg0) {
	//System.out.println("Window Opened");
    }
 
	
    private void setLookFeel(){
        
        UIManager.put("OptionPane.background",         DEFAULT_COLOUR);
        UIManager.put("Panel.background",              DEFAULT_COLOUR);
        UIManager.put("Button.background",             DEFAULT_COLOUR);
        UIManager.put("CheckBoxMenuItem.background",   DEFAULT_COLOUR);
        UIManager.put("SplitPane.background",          DEFAULT_COLOUR);
        UIManager.put("Table.background",              DEFAULT_COLOUR);
        UIManager.put("Menu.background",               DEFAULT_COLOUR);
        UIManager.put("MenuItem.background",           DEFAULT_COLOUR);
        UIManager.put("TextField.background",          DEFAULT_COLOUR);
        UIManager.put("ComboBox.background",           DEFAULT_COLOUR);
        UIManager.put("TabbedPane.background",         DEFAULT_COLOUR);
        UIManager.put("TabbedPane.selected",           DEFAULT_COLOUR);
        UIManager.put("MenuBar.background",            DEFAULT_COLOUR);
        UIManager.put("window.background",             DEFAULT_COLOUR);
        UIManager.put("TextPane.background",           LOG_COLOUR);
        UIManager.put("Tree.background",               LOG_COLOUR);
        UIManager.put("RadioButtonMenuItem.background",DEFAULT_COLOUR);
        UIManager.put("RadioButton.background",        DEFAULT_COLOUR);
        
        UIManager.put("Table.font",                    DEFAULT_FONT);
        UIManager.put("TabbedPane.font",               DEFAULT_FONT);
        UIManager.put("OptionPane.font",               DEFAULT_FONT);
        UIManager.put("Menu.font",                     DEFAULT_FONT);
        UIManager.put("MenuItem.font",                 DEFAULT_FONT);
        UIManager.put("Button.font",                   DEFAULT_FONT);
        UIManager.put("ComboBox.font",                 DEFAULT_FONT);
        UIManager.put("RadioButtonMenuItem.font",      DEFAULT_FONT);
        UIManager.put("RadioButton.font",              DEFAULT_FONT);
        
    }	

    public static void main(String[] args){
	FilterWheel aWheel = new FilterWheel();
	String[] exampleNames = {"u'","g'","r'","i'","z'","clear"};
    	WheelController control = new WheelController(exampleNames, aWheel);
    }
    
}
