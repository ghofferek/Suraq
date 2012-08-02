package at.iaik.suraq.util;

import java.io.File;
import java.io.FileWriter;
import java.util.HashSet;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;

public class DebugHelper
{
    private static DebugHelper _instance = null;
    private static long cnt = -2;
    private static String _name = "";
    
    public static String getName()
    {
        return _name;
    }
    

    public static Set<Token> predicates = new HashSet<Token>();
    public static Set<Token> functions = new HashSet<Token>();
    
    public static boolean filter(String name)
    {
        if(name.equals(_name))
        {
            return true;
        }
        
        if(cnt==-1)
            return false;
        else if(cnt==-2)
        {
            System.out.println("This is an filter for the n-th element. It will only return true for this element.");
            System.out.println("Please enter a ID (0 for first, 1 for second,...)");
            java.util.Scanner sc = new java.util.Scanner(System.in);
            cnt = sc.nextLong();
        }
        if(cnt-- == 0)
        {
            System.err.println("Filtered name is: "+name);
            _name = name;
            return true;
        }
        return false;
    }
    
    public static DebugHelper getInstance()
    {
        if(_instance==null)
            _instance = new DebugHelper();
        return _instance;
    }
    
    String folder = "./";

    public void setFolder(String folder) {
        try {
            File path = new File(folder);
            if (!path.exists()) {
                System.out.println("Folder " + folder + "created.");
                path.mkdirs();
            }
            if (!path.isDirectory())
                throw new RuntimeException("given folder is no path");
            this.folder = folder;
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    public void formulaToFile(Formula formula, String filename)
    {
        stringtoFile(formula.toString(), filename);
    }
    
    public void stringtoFile(String text, String filename)
    {
        System.out.println("* File written to '" + folder+filename + "'");
        try{
            File debugFile1 = new File(folder+filename);
            FileWriter fstream = new FileWriter(debugFile1);
            fstream.write(text);
            fstream.close();
        }
        catch(Exception ex)
        {
            ex.printStackTrace();
        }
    }
    
}
