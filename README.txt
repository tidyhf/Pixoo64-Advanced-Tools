Step 1: Install Python
If you don't have Python installed, you'll need to get it from the official website.

Go to the official Python website:
https://www.python.org/downloads/

Download the latest Python installer (the big yellow button).

Run the installer. This is the most important step:
On the first screen of the installer, make sure you check the box at the bottom that says "Add Python to PATH". This will allow you to run the necessary commands easily.

Click "Install Now" and follow the on-screen prompts to complete the installation.

Step 2: Install Required Libraries
Now we'll install all the libraries the application needs to run.

Make sure the Pixoo64Tools.py script and the requirements.txt file are in the same folder.

Open the Command Prompt. You can do this by opening your Start Menu, typing cmd, and pressing Enter.

In the Command Prompt, you first need to navigate to the folder where you saved the script. A simple way to do this is to type cd (which means "change directory"), followed by a space, and then drag the folder from your File Explorer directly into the Command Prompt window. It will paste the full path for you.
It should look something like this:
cd C:\Users\YourName\Downloads\Pixoo-Tools

Press Enter.

Now that you are in the correct folder, copy and paste the following command into the Command Prompt and press Enter:
pip install -r requirements.txt

This command tells Python's package installer (pip) to read the requirements.txt file and install everything listed inside it. Wait for it to finish.

Step 3: Run the Application!
Once the installation is complete, you're ready to go!

In the same Command Prompt window (and in the same folder), simply type the following command and press Enter:
python Pixoo64Tools.py

The application window should now appear. The first time you successfully connect to your Pixoo's IP address, the app will save it for you so you don't have to enter it every time.

Enjoy the tool!