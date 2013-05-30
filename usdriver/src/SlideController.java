package warwick.marsh.ultracam.usdriver;

import java.lang.Void;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.SwingWorker;

import java.awt.*;              //for layout managers and more
import java.awt.event.*;        //for action events

import java.net.*;
import java.io.*;

public class SlideController extends JFrame
        implements ActionListener {
    
    private String newline = "\n";
    
    // Colours and Fonts
    public static final Color DEFAULT_COLOUR    = new Color(220, 220, 255);
    public static final Color SEPARATOR_BACK    = new Color(100, 100, 100);
    public static final Color SEPARATOR_FORE    = new Color(150, 150, 200);
    public static final Color LOG_COLOUR        = new Color(240, 230, 255);
    public static final Color ERROR_COLOUR      = new Color(255, 0,   0  );
    public static final Color WARNING_COLOUR    = new Color(255, 100, 0  );
    public static final Color GO_COLOUR         = new Color(0,   255, 0  );
    public static final Color STOP_COLOUR       = new Color(255, 0,   0  );
    public static final Font DEFAULT_FONT = new Font("Dialog", Font.BOLD, 12);
    
    private String units = "px";
    
    private javax.swing.JLabel jLabel1;
    private javax.swing.JPanel jPanel1;
    private javax.swing.JScrollPane jScrollPane1;
    private javax.swing.ButtonGroup buttonGroup1;
    private JTextField amountField;
    private JButton gotoButton;
    private JButton addButton;
    private JButton subButton;
    private JButton parkButton;
    private JButton homeButton;
    private JButton resetButton;
    private JButton posButton;
    private JButton closeButton;
    private JButton enableButton;
    private JButton disableButton;
    private JButton restoreButton;
    JButton[] buttons = {gotoButton, addButton,
			 subButton, parkButton,
			 homeButton, resetButton,
			 posButton,  closeButton,
			 enableButton, disableButton,
			 restoreButton
    };
    private JRadioButton mmButton;
    private JRadioButton msButton;
    private JRadioButton pxButton;
    JRadioButton[] radioButtons = {mmButton, msButton,
    pxButton};
    
    JTextPane textPane;
    
    String command;
    
    public SlideController() {
        initComponents();
        setVisible(true);
    }
    
    private void initComponents() {
        
        buttonGroup1 = new javax.swing.ButtonGroup();
        jPanel1 = new javax.swing.JPanel();
        mmButton = new javax.swing.JRadioButton();
        msButton = new javax.swing.JRadioButton();
        pxButton = new javax.swing.JRadioButton();
        amountField = new javax.swing.JTextField();
        jLabel1 = new javax.swing.JLabel();
        gotoButton = new javax.swing.JButton();
        addButton = new javax.swing.JButton();
        subButton = new javax.swing.JButton();
        homeButton = new javax.swing.JButton();
        parkButton = new javax.swing.JButton();
        posButton = new javax.swing.JButton();
        resetButton = new javax.swing.JButton();
        jScrollPane1 = new javax.swing.JScrollPane();
        textPane = new javax.swing.JTextPane();
        closeButton = new javax.swing.JButton();
        enableButton = new javax.swing.JButton();
        disableButton = new javax.swing.JButton();
        restoreButton = new javax.swing.JButton();
        
        //setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
        setResizable(false);
        jPanel1.setBorder(javax.swing.BorderFactory.createTitledBorder(javax.swing.BorderFactory.createEtchedBorder(), "Units", javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION, javax.swing.border.TitledBorder.DEFAULT_POSITION, DEFAULT_FONT));
        buttonGroup1.add(mmButton);
        mmButton.setText("mm");
        mmButton.setToolTipText("millimeters");
        mmButton.setBorder(javax.swing.BorderFactory.createEmptyBorder(0, 0, 0, 0));
        mmButton.setMargin(new java.awt.Insets(0, 0, 0, 0));
        
        buttonGroup1.add(msButton);
        msButton.setText("ms");
        msButton.setToolTipText("microsteps");
        msButton.setBorder(javax.swing.BorderFactory.createEmptyBorder(0, 0, 0, 0));
        msButton.setMargin(new java.awt.Insets(0, 0, 0, 0));
        
        buttonGroup1.add(pxButton);
        pxButton.setText("px");
        pxButton.setToolTipText("choose pixel units");
        pxButton.setBorder(javax.swing.BorderFactory.createEmptyBorder(0, 0, 0, 0));
        pxButton.setContentAreaFilled(false);
        pxButton.setMargin(new java.awt.Insets(0, 0, 0, 0));
        pxButton.setSelected(true);
        
        javax.swing.GroupLayout jPanel1Layout = new javax.swing.GroupLayout(jPanel1);
        jPanel1.setLayout(jPanel1Layout);
        jPanel1Layout.setHorizontalGroup(
                jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                .addGroup(jPanel1Layout.createSequentialGroup()
                .addGap(32, 32, 32)
                .addComponent(mmButton)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 73, Short.MAX_VALUE)
                .addComponent(msButton)
                .addGap(76, 76, 76)
                .addComponent(pxButton, javax.swing.GroupLayout.PREFERRED_SIZE, 45, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addGap(46, 46, 46))
                );
        
        jPanel1Layout.linkSize(javax.swing.SwingConstants.HORIZONTAL, new java.awt.Component[] {mmButton, msButton, pxButton});
        
        jPanel1Layout.setVerticalGroup(
                jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                .addGroup(jPanel1Layout.createSequentialGroup()
                .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                .addComponent(msButton)
                .addComponent(pxButton)
                .addComponent(mmButton))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
                );
        
        amountField.setToolTipText("enter distance to move here");
        
        jLabel1.setText("Amount:");
        gotoButton.setText("goTo");
        addButton.setText("+");
        subButton.setText("-");
        homeButton.setText("home");
        parkButton.setText("park");
        posButton.setText("position");
        resetButton.setText("reset");
        closeButton.setText("Close");
        enableButton.setText("enable");
        disableButton.setText("disable");
        restoreButton.setText("restore");

	// tooltips for non-obvious buttons
	enableButton.setToolTipText("enable potentiometer");
	disableButton.setToolTipText("disable potentiometer");
	restoreButton.setToolTipText("restore to factory settings");
        
        // add action commands
        amountField.setActionCommand("amount");
        gotoButton.setActionCommand("goto");
        addButton.setActionCommand("add");
        subButton.setActionCommand("sub");
        parkButton.setActionCommand("park");
        homeButton.setActionCommand("home");
        resetButton.setActionCommand("reset");
        posButton.setActionCommand("pos");
        mmButton.setActionCommand("mm");
        msButton.setActionCommand("ms");
        pxButton.setActionCommand("px");
        closeButton.setActionCommand("close");
        enableButton.setActionCommand("enable");
        disableButton.setActionCommand("disable");
        restoreButton.setActionCommand("restore");
        
        amountField.addActionListener(this);
        gotoButton.addActionListener(this);
        addButton.addActionListener(this);
        subButton.addActionListener(this);
        parkButton.addActionListener(this);
        homeButton.addActionListener(this);
        resetButton.addActionListener(this);
        posButton.addActionListener(this);
        mmButton.addActionListener(this);
        msButton.addActionListener(this);
        pxButton.addActionListener(this);
        closeButton.addActionListener(this);
        enableButton.addActionListener(this);
        disableButton.addActionListener(this);
        restoreButton.addActionListener(this);
        
        
        jScrollPane1.setHorizontalScrollBarPolicy(javax.swing.ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
        textPane.setAutoscrolls(false);
        textPane.setMinimumSize(new java.awt.Dimension(80, 21));
        jScrollPane1.setViewportView(textPane);
        textPane.updateUI();
        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
				  layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				  .addGroup(
					    layout.createSequentialGroup()
					    .addGroup(
						      layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
						      .addGroup(
								layout.createSequentialGroup()
								.addGap(53, 53, 53)
								.addComponent(jLabel1)
								)
						      .addGroup(
								layout.createSequentialGroup()
								.addGap(28, 28, 28)
								.addGroup(
									  layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
									  .addComponent(jPanel1, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
									  .addGroup(
										    layout.createSequentialGroup()
										    .addComponent(homeButton)
										    .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
										    .addGroup(
											      layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
											      .addComponent(enableButton)
											      .addComponent(parkButton)
											      .addComponent(gotoButton, javax.swing.GroupLayout.DEFAULT_SIZE, 89, Short.MAX_VALUE)
											      .addComponent(amountField, javax.swing.GroupLayout.PREFERRED_SIZE, 82, javax.swing.GroupLayout.PREFERRED_SIZE)
											      )
										    .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
										    .addGroup(
											      layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
											      .addComponent(disableButton)
											      .addComponent(posButton)
											      .addComponent(addButton)
											      )
										    .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
										    .addGroup(
											      layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
											      .addComponent(subButton)
											      .addComponent(resetButton)
											      .addComponent(restoreButton)
											      )
										    )
									  )
								.addGap(21, 21, 21))
						      .addGroup(
								layout.createSequentialGroup()
								.addContainerGap()
								.addComponent(jScrollPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 411, Short.MAX_VALUE)
								)
						      .addGroup(
								javax.swing.GroupLayout.Alignment.TRAILING, layout.createSequentialGroup()
								.addContainerGap()
								.addComponent(closeButton, javax.swing.GroupLayout.PREFERRED_SIZE, 84, javax.swing.GroupLayout.PREFERRED_SIZE)
								)
						      )
					    .addContainerGap()
					    )
				  );
        
        layout.linkSize(javax.swing.SwingConstants.HORIZONTAL, new java.awt.Component[] {addButton, gotoButton, homeButton, parkButton, posButton, resetButton, subButton, restoreButton, enableButton, disableButton});
        
        layout.setVerticalGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				.addGroup(layout.createSequentialGroup()
					  .addContainerGap()
					  .addComponent(jPanel1, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
					  .addGap(17, 17, 17)
					  .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
						    .addComponent(jLabel1)
						    .addComponent(amountField, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
						    )
					  .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
					  .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
						    .addGroup(layout.createSequentialGroup()
							      .addComponent(gotoButton)
							      .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
							      .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
									.addComponent(homeButton)
									.addComponent(parkButton)
									)
							      .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
							      .addComponent(enableButton)
							      )
						    .addGroup(layout.createSequentialGroup()
							      .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
									.addComponent(addButton)
									.addComponent(subButton)
									)
							      .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
							      .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
									.addComponent(posButton)
									.addComponent(resetButton)
									)
							      .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
							      .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
									.addComponent(disableButton)
									.addComponent(restoreButton)
									)							      
							      )
						    )
					  .addGap(21, 21, 21)
					  .addComponent(jScrollPane1, javax.swing.GroupLayout.DEFAULT_SIZE, 234, Short.MAX_VALUE)
					  .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
					  .addComponent(closeButton)
					  .addContainerGap()
					  )
				);
        
        layout.linkSize(javax.swing.SwingConstants.VERTICAL, new java.awt.Component[] {addButton, gotoButton, homeButton, parkButton, posButton, resetButton, subButton, restoreButton, enableButton, disableButton});
        
        pack();
    }
    
    class SlideTask extends SwingWorker<String, Void>{
	@Override
        public String doInBackground(){
            sendToSlide(command);
            return command;
        }
    };
    
    public void actionPerformed(ActionEvent e){
        if(e.getActionCommand().equals("goto")){
	    command="pos=" + amountField.getText() + units;
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("add")){
            command="+" + amountField.getText() + units;
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute();
        }else if(e.getActionCommand().equals("sub")){
            command="-"  + amountField.getText() + units;
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("park")){
            command="park";
	    textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("pos")){
	    command="position";
	    textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("home")){
            command="home";
	    textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("reset")){
            command="reset";
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("enable")){
            command="enable";
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("disable")){
            command="disable";
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("restore")){
            command="restore";
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("stop")){
            command="stop";
            textPane.setText("Sending slide command: " + command);
	    (new SlideTask()).execute(); 
        }else if(e.getActionCommand().equals("mm")){
            units = "mm";
        }else if(e.getActionCommand().equals("ms")){
            units = "ms";
        }else if(e.getActionCommand().equals("px")){
            units = "px";
        }else if(e.getActionCommand().equals("close")){
            this.setVisible(false);
        }
    }
    
    
    private boolean sendToSlide(final String cmd) {
        
        
        // send slide command on it's own process
        try{
	    String stdout=null;
	    String stderr=null;
	    String line=null;

	    Process p = Runtime.getRuntime().exec("/home/observer/slide/slide "+cmd);
	    BufferedReader bri = new BufferedReader
		(new InputStreamReader(p.getInputStream()));
	    BufferedReader bre = new BufferedReader
		(new InputStreamReader(p.getErrorStream()));
	    while ((line = bri.readLine()) != null) {
		if(stdout == null){
		    stdout = line;
		}else{
		    stdout += ("\n"+line) ;
		}
	    }
	    bri.close();
	    while ((line = bre.readLine()) != null) {
		if(stderr == null){
		    stderr = line;
		}else{
		    stderr += ("\n"+line);
		}
	    }
	    bre.close();
	    p.waitFor();
	    if(stderr == null){
		textPane.setContentType("text/html");
		textPane.setText(stdout);
		textPane.setBackground(LOG_COLOUR);
	    }else{
		textPane.setContentType("text/html");
		textPane.setText(stderr);
		textPane.setBackground(ERROR_COLOUR);
	    }
        } catch(Exception e) {
	    textPane.setContentType("text/html");
            textPane.setText("Command to slide control script failed: " + e);
            textPane.setBackground(ERROR_COLOUR);
        }
        
        return true;
        
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
    
}
