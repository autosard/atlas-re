cd ..
artifact/make-source.sh
cd artifact
mkdir -p artifact
cp Dockerfile artifact/
cp README.md artifact/
cp LICENSE.txt artifact/

rm artifact.zip
zip -r artifact.zip \
    artifact/README.md \
    artifact/LICENSE.txt \
    artifact/Dockerfile \
    artifact/image.tar.gz \
    artifact/source
