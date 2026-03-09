# Web-App
As a quick solution you may use the following web application <https://jscoq.github.io/wa/scratchpad.html>

# Setup Linux
On Linux you have multiple options: 
- If you use the proprietary VSCode and prefer to have your environment containerized, you may follow the instructions under `Setup Windows & Mac`
- If you prefer the open Source VSCodium you may install:
    1. Ocaml `sudo apt update && sudo apt install ocaml -y`,
    2. Coq and the vscoq language server `opam update && opam install -y vscoq-language-server`, 
    2. and the extension `maximedenes.vscoq`.
- Finally you may also use CoqIDE which is bundeled with the Coq Platform <https://github.com/coq/platform/blob/main/doc/README_Linux.md>

# Setup Windows & Mac

## Install Software
1. Install `docker` and `docker-compose`
2. Install `vscode`
3. Install the extension `ms-vscode-remote.remote-containers`
4. Optionally install the extension `ms-azuretools.vscode-docker`
5. Install the extension `maximedenes.vscoq` in version `2.2.1`
    - Navigate to the extensions menu.
    - Right-click on `VsCoq` and choose `Install Specific Version`

## Start Container
1. Open the directory containing the file `docker-compoe.yml` in `vscode`
2. Run `docker-compose up -d` or, if you have installed the extension `ms-azuretools.vscode-docker` simply open `docker-compose.yml` and click `RunAllServices`.

## Connect to the Container
1. In `vscode` click on `Open a Remote Window`. It's the button with the symbols `><` in the lower left corner.
2. Choose `Attach to Running Container` and choose the container coq (the exact name may vary)
