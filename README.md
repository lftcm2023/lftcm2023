Lean for the Curious Mathematician 2023
=======================================
Düsseldorf, 4-8 Sep. 2023

This repository contains the exercises for the LftCM2023 workshop. It is based on
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).
(see also its [Github Repo](https://github.com/leanprover-community/mathematics_in_lean))

The workshops website: [LftCM2023 website](https://lftcm2023.github.io/)


## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. If you have not logged in since you installed Lean and mathlib, then you may need to first type `source ~/.profile` or `source ~/.bash_profile` depending on your OS.

3. Go the the directory where you would like this package to live.

4. Run `git clone https://github.com/lftcm2023/lftcm2023.git`.

5. Run `cd lftcm2023`

6. Run `lake exe cache get`

7. Launch VS Code, either through your application menu or by typing `code .`. (MacOS users need to take a one-off [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line) to be able to launch VS Code from the command line.)

8. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder `lftcm2023` (not one of its subfolders).

9. Using the file explorer on the left-hand side. The `LftCM` directory contains the lecture and exercise files.

10. The lessons will be added as we go during the week. You can update the repository by typing
   `git pull` inside the `lftcm2023` folder.



## To use this repository with Gitpod

If you have a Gitpod account or are willing to sign up for one,
just point your browser to [https://gitpod.io/#/https://github.com/lftcm2023/lftcm2023](https://gitpod.io/#/https://github.com/lftcm2023/lftcm2023).
This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` as above.

Gitpod gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab.

To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/).
If you change the filter from Active to All, you will see all your recent workspaces. You can pin a workspace to keep it on the list of active ones.
