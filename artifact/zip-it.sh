cd ..
artifact/make-source.sh
cd artifact
mkdir -p artifact
docker save artifact10 | gzip > artifact/image.tar.gz
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
